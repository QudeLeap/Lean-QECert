import QEC.Coding.ChainComplex.Cohomology
import QEC.Coding.Stabilizer.LocalHamiltonian
import QEC.Locality.Graph.Core
/-!
# Finite interfaces for the BDL26 multiscale decoder

This module records only the finite data consumed by the later BDL26 decoder
proofs.  A level is represented by the existing three-term
`ChainComplexData`; its cochain maps are the transposes of the stored boundary
maps.  Thus this file is an adapter around the M3 chain/cochain API rather than
a second global code model.

The records below intentionally contain no correctness, probability, or
logical-preservation conclusions.  Those statements belong to later M12/M13
proof nodes.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder

open scoped BigOperators

universe u v w x y z a

abbrev BDL26Field := ZMod 2

/-- A level index for a depth-`depth` decoder, including the base level. -/
abbrev LevelIndex (depth : Nat) := Fin (depth + 1)

/-- An adjacent replacement/coarse-graining index. -/
abbrev StepIndex (depth : Nat) := Fin depth

/-- The two replacement labels used by the alternating BDL26 family. -/
inductive ReplacementKind where
  | rx
  | rz
  deriving DecidableEq, Repr

/-- The three vertex roles in one oriented level graph. -/
inductive LevelVertexKind where
  | x
  | q
  | z
  deriving DecidableEq, Repr

/-- The forward replacement selected at a level index.

Even forward steps are `R_X`; odd forward steps are `R_Z`, matching the
construction contract.  A coarse-graining input at level `i+1` therefore uses
the map selected at its predecessor `i`.
-/
def replacementKind (i : Nat) : ReplacementKind :=
  if i % 2 = 0 then .rx else .rz

@[simp]
theorem replacementKind_zero : replacementKind 0 = .rx := by
  simp [replacementKind]

@[simp]
theorem replacementKind_one : replacementKind 1 = .rz := by
  simp [replacementKind]

@[simp]
theorem replacementKind_two : replacementKind 2 = .rx := by
  simp [replacementKind]

variable {depth : Nat}

/--
An indexed finite family of three-term chain complexes.

The boundary maps use the orientation already present in `ChainComplexData`:
`C¹ → C⁰` and `C² → C¹`.  The BDL26 cochain maps exposed below are their
finite-coordinate transposes, so the existing M3 chain/cochain semantics are
reused exactly.
-/
structure BDL26CochainFamily
    (depth : Nat)
    (C0 C1 C2 : LevelIndex depth → Type u)
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)] where
  complex : ∀ i : LevelIndex depth,
    ChainComplexData BDL26Field
      (Word BDL26Field (C0 i))
      (Word BDL26Field (C1 i))
      (Word BDL26Field (C2 i))

namespace BDL26CochainFamily

variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

abbrev Cochain0 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C0 i)

abbrev Cochain1 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C1 i)

abbrev Cochain2 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C2 i)

/-- The existing M3 cochain coboundary `δ⁰`, obtained by transposition. -/
noncomputable def coboundary0 (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : F.Cochain0 i →ₗ[BDL26Field] F.Cochain1 i :=
  wordLinearMapTranspose (F.complex i).boundary1

/-- The existing M3 cochain coboundary `δ¹`, obtained by transposition. -/
noncomputable def coboundary1 (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : F.Cochain1 i →ₗ[BDL26Field] F.Cochain2 i :=
  wordLinearMapTranspose (F.complex i).boundary2

/-- The level-`i` syndrome carrier `B²ᵢ = im(δ¹ᵢ)`. -/
noncomputable def syndromeSubmodule (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : Submodule BDL26Field (F.Cochain2 i) :=
  LinearMap.range (F.coboundary1 i)

/-- A finite level-indexed syndrome, represented as a subtype of `B²ᵢ`. -/
abbrev Syndrome (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :=
  {s : F.Cochain2 i // s ∈ F.syndromeSubmodule i}

/-- A level-indexed correction/error cochain in `C¹ᵢ`. -/
abbrev Correction (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := F.Cochain1 i

theorem wordLinearMapTranspose_zero_local
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] :
    wordLinearMapTranspose (0 : Word F ι →ₗ[F] Word F κ) = 0 := by
  classical
  apply LinearMap.ext
  intro y
  ext i
  simp [wordLinearMapTranspose]

theorem coboundary1_comp_coboundary0
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :
    (F.coboundary1 i).comp (F.coboundary0 i) =
      (0 : F.Cochain0 i →ₗ[BDL26Field] F.Cochain2 i) := by
  calc
    (F.coboundary1 i).comp (F.coboundary0 i) =
        wordLinearMapTranspose ((F.complex i).boundary1.comp
          (F.complex i).boundary2) := by
      symm
      exact wordLinearMapTranspose_comp
        (g := (F.complex i).boundary1) (f := (F.complex i).boundary2)
    _ = wordLinearMapTranspose
        (0 : Word BDL26Field (C2 i) →ₗ[BDL26Field] Word BDL26Field (C0 i)) := by
      exact congrArg wordLinearMapTranspose (F.complex i).boundary_squared
    _ = 0 := wordLinearMapTranspose_zero_local

@[simp]
theorem syndromeSubmodule_mem
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) :
    (s : F.Cochain2 i) ∈ F.syndromeSubmodule i :=
  s.property

/-- Syndrome support, using the project-wide finite-word support definition. -/
noncomputable def syndromeSupport
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) : Finset (C2 i) := by
  classical
  exact hammingSupport (s : F.Cochain2 i)

/-- The finite syndrome weight used by the BDL26 counting interfaces. -/
noncomputable def syndromeWeight
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) : Nat := by
  classical
  exact HammingWeight (s : F.Cochain2 i)

/-- Correction support, using the project-wide finite-word support definition. -/
noncomputable def correctionSupport
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (f : F.Correction i) : Finset (C1 i) := by
  classical
  exact hammingSupport f

/-- The finite correction/error weight used by later decoder interfaces. -/
noncomputable def correctionWeight
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (f : F.Correction i) : Nat := by
  classical
  exact HammingWeight f

@[simp]
theorem syndromeWeight_zero
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :
    syndromeWeight F i (⟨0, by simp [syndromeSubmodule]⟩ : F.Syndrome i) = 0 := by
  simp [syndromeWeight]

@[simp]
theorem correctionWeight_zero
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : correctionWeight F i (0 : F.Correction i) = 0 := by
  simp [correctionWeight]

end BDL26CochainFamily

open BDL26CochainFamily

/-- A cochain map between two adjacent finite levels. -/
structure BDL26CochainMap
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (F : BDL26CochainFamily depth C0 C1 C2) (i : StepIndex depth) where
  map0 : F.Cochain0 i.castSucc →ₗ[BDL26Field] F.Cochain0 i.succ
  map1 : F.Cochain1 i.castSucc →ₗ[BDL26Field] F.Cochain1 i.succ
  map2 : F.Cochain2 i.castSucc →ₗ[BDL26Field] F.Cochain2 i.succ
  commutes_coboundary0 :
    (F.coboundary0 i.succ).comp map0 = map1.comp (F.coboundary0 i.castSucc)
  commutes_coboundary1 :
    (F.coboundary1 i.succ).comp map1 = map2.comp (F.coboundary1 i.castSucc)

namespace BDL26CochainMap

variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {F : BDL26CochainFamily depth C0 C1 C2}
variable {i : StepIndex depth}

/-- The selected map sends a lower-level syndrome into the next syndrome space. -/
def mapSyndrome (M : BDL26CochainMap F i)
    (s : F.Syndrome i.castSucc) : F.Syndrome i.succ := by
  refine ⟨M.map2 s.1, ?_⟩
  change M.map2 (s : F.Cochain2 i.castSucc) ∈
    LinearMap.range (F.coboundary1 i.succ)
  rcases s.property with ⟨f, hf⟩
  refine ⟨M.map1 f, ?_⟩
  have h := LinearMap.congr_fun M.commutes_coboundary1 f
  simp only [LinearMap.comp_apply] at h
  rw [hf] at h
  exact h

@[simp]
theorem mapSyndrome_coe (M : BDL26CochainMap F i)
    (s : F.Syndrome i.castSucc) :
    (M.mapSyndrome s : F.Cochain2 i.succ) = M.map2 s :=
  rfl

end BDL26CochainMap

/-- A finite decoder family with the two alternating adjacent-level maps. -/
structure BDL26DecoderData
    (depth : Nat)
    (C0 C1 C2 : LevelIndex depth → Type u)
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)] where
  family : BDL26CochainFamily depth C0 C1 C2
  rxMap : ∀ i : StepIndex depth, BDL26CochainMap family i
  rzMap : ∀ i : StepIndex depth, BDL26CochainMap family i

namespace BDL26DecoderData

variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

/-- The forward map chosen by the audited alternating parity convention. -/
def selectedMap (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :
    BDL26CochainMap D.family i :=
  if replacementKind i.val = .rx then D.rxMap i else D.rzMap i

@[simp]
theorem selectedMap_zero
    (D : BDL26DecoderData depth C0 C1 C2)
    (h : 0 < depth) :
    D.selectedMap ⟨0, h⟩ = D.rxMap ⟨0, h⟩ := by
  simp [selectedMap]

@[simp]
theorem selectedMap_one
    (D : BDL26DecoderData depth C0 C1 C2)
    (h : 1 < depth) :
    D.selectedMap ⟨1, h⟩ = D.rzMap ⟨1, h⟩ := by
  simp [selectedMap]

end BDL26DecoderData

/-! ## Raw finite coordinate actions

The M13 raw-geometry contract names the finite coordinate actions separately
from the cochain-map commutation laws above.  A basis-action record is only a
finite table of images and its compatibility equation; it carries no section,
transport, or decoder property.
-/

structure TypedFiniteBasisAction
    {Source Target : Type u}
    [Fintype Source] [Fintype Target]
    (map : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target) where
  basisImage : Source → Word BDL26Field Target
  basis_action : ∀ source,
    map (canonicalBasisWord source) = basisImage source

/-- The four selected RX/RZ degree-one and degree-two finite basis tables. -/
structure TypedCoordinateBasisActions
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) where
  rxDegreeOne : TypedFiniteBasisAction (D.rxMap i).map1
  rxDegreeTwo : TypedFiniteBasisAction (D.rxMap i).map2
  rzDegreeOne : TypedFiniteBasisAction (D.rzMap i).map1
  rzDegreeTwo : TypedFiniteBasisAction (D.rzMap i).map2

namespace TypedCoordinateBasisActions

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}

@[simp]
theorem rxDegreeOne_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C1 i.castSucc) :
    (D.rxMap i).map1 (canonicalBasisWord c) = A.rxDegreeOne.basisImage c :=
  A.rxDegreeOne.basis_action c

@[simp]
theorem rxDegreeTwo_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C2 i.castSucc) :
    (D.rxMap i).map2 (canonicalBasisWord c) = A.rxDegreeTwo.basisImage c :=
  A.rxDegreeTwo.basis_action c

@[simp]
theorem rzDegreeOne_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C1 i.castSucc) :
    (D.rzMap i).map1 (canonicalBasisWord c) = A.rzDegreeOne.basisImage c :=
  A.rzDegreeOne.basis_action c

@[simp]
theorem rzDegreeTwo_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C2 i.castSucc) :
    (D.rzMap i).map2 (canonicalBasisWord c) = A.rzDegreeTwo.basisImage c :=
  A.rzDegreeTwo.basis_action c

end TypedCoordinateBasisActions

/-- A level-indexed syndrome/correction state. -/
structure LevelState
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth) where
  syndrome : D.family.Syndrome i
  correction : D.family.Correction i

/-- A checked coarse-graining relation at an adjacent level.

The relation is data about one finite input/output record.  It is not a
correctness theorem and contains no probability conclusion.
-/
structure CoarseGrainingStep
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) where
  input : D.family.Syndrome i.succ
  correction : D.family.Correction i.succ
  coarse : D.family.Syndrome i.castSucc
  relation : (input : D.family.Cochain2 i.succ) =
    D.family.coboundary1 i.succ correction +
      (D.selectedMap i).map2 coarse

namespace CoarseGrainingStep

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}

@[simp]
theorem selected_replacement_kind
    (i : StepIndex depth) :
    replacementKind i.val = .rx ∨ replacementKind i.val = .rz := by
  unfold replacementKind
  split <;> simp_all

end CoarseGrainingStep

/-- The recursive level-zero syndrome input in a single coarse-graining step. -/
abbrev RecursiveBaseLevelInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) :=
  D.family.Syndrome (0 : LevelIndex depth)

/-- A recursive level-zero correction record, retaining only the displayed
coboundary relation and making no correction claim. -/
structure RecursiveBaseLevelCorrection
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) where
  input : RecursiveBaseLevelInput D
  correction : D.family.Correction (0 : LevelIndex depth)
  relation : (input : D.family.Cochain2 (0 : LevelIndex depth)) =
    D.family.coboundary1 (0 : LevelIndex depth) correction

/-- A finite adapter from syndrome coordinates to selected Hamiltonian checks.

The equivalence is the only identification made here: it reindexes a finite
`C²` syndrome by the actual check family of an existing
`LocalStabilizerHamiltonian`.  No Hamiltonian energy or decoding theorem is
introduced. -/
structure HamiltonianSyndromeAdapter
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {physical : Type v} [Fintype physical] [DecidableEq physical]
    {check : Type w} [Fintype check]
    (D : BDL26DecoderData depth C0 C1 C2)
    (H : StabilizerCode.LocalStabilizerHamiltonian (ι := physical) (κ := check))
    (i : LevelIndex depth) where
  coordinateEquiv : C2 i ≃ check

namespace HamiltonianSyndromeAdapter

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {physical : Type v} [Fintype physical] [DecidableEq physical]
variable {check : Type w} [Fintype check]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {H : StabilizerCode.LocalStabilizerHamiltonian
  (ι := physical) (κ := check)}
variable {i : LevelIndex depth}

/-- Reindex a finite syndrome word by the selected Hamiltonian checks. -/
def reindexSyndrome
    (A : HamiltonianSyndromeAdapter D H i)
    (s : D.family.Syndrome i) : Word BDL26Field check :=
  fun j => (s : D.family.Cochain2 i) (A.coordinateEquiv.symm j)

/-- The actual local support attached to one selected Hamiltonian check. -/
def selectedGeneratorSupport
    (_A : HamiltonianSyndromeAdapter D H i) (j : check) : Finset physical :=
  H.generatorSupport j

@[simp]
theorem selectedGeneratorSupport_eq
    (A : HamiltonianSyndromeAdapter D H i) (j : check) :
    A.selectedGeneratorSupport j = H.generatorSupport j :=
  rfl

end HamiltonianSyndromeAdapter

/-- A finite directed graph with explicit no-loop structure.

Edges are booleans so the finite distance operation below is executable on a
finite graph.  The coercion `edge u v = true` is the directed adjacency
predicate used by the path search.
-/
structure DirectedGraph (V : Type v) [Fintype V] [DecidableEq V] where
  edge : V → V → Bool
  loopless : ∀ v, edge v v = false

namespace DirectedGraph

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Directed paths are indexed by their finite length. -/
inductive Path (G : DirectedGraph V) : V → V → Nat → Prop
  | nil (v : V) : Path G v v 0
  | cons {u v w : V} {n : Nat} :
      G.edge u v = true → Path G v w n → Path G u w (n + 1)

/-- Whether `v` is reachable from `u` by a directed path of length at most
`steps`.  The recursion enumerates the finite vertex type, so the operation is
executable rather than an abstract infimum over paths. -/
def reachableWithin (G : DirectedGraph V) : Nat → V → V → Bool
  | 0, u, v => decide (u = v)
  | steps + 1, u, v =>
      reachableWithin G steps u v ||
        decide (∃ w : V, G.edge u w = true ∧ reachableWithin G steps w v = true)

/-- The shortest directed path length, with `⊤` when no path exists.

Any reachable vertex in a finite graph has a simple path of length at most the
number of vertices, so searching `range (card V + 1)` is exact. -/
def distanceAux (G : DirectedGraph V) (u v : V) : Nat → Option Nat
  | 0 => if reachableWithin G 0 u v then some 0 else none
  | steps + 1 =>
      match distanceAux G u v steps with
      | some n => some n
      | none => if reachableWithin G (steps + 1) u v then some (steps + 1) else none

def distance (G : DirectedGraph V) (u v : V) : WithTop Nat :=
  match distanceAux G u v (Fintype.card V) with
  | some n => n
  | none => ⊤

end DirectedGraph

/-- A finite local region centred at one graph node. -/
structure LocalRegion (V : Type v) [Fintype V] [DecidableEq V] where
  center : V
  vertices : Finset V

namespace LocalRegion

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The exact radius-`r` directed input region used by local-computability. -/
def directedNeighborhood
    (G : DirectedGraph V) (center : V) (radius : Nat) : Finset V := by
  exact Finset.univ.filter fun v => DirectedGraph.distance G v center ≤ radius

/-- The source radius-one correction region. -/
def correctionRegion
    (G : DirectedGraph V) (center : V) : LocalRegion V :=
  ⟨center, directedNeighborhood G center 1⟩

/-- The source radius-two coarse-syndrome region. -/
def syndromeRegion
    (G : DirectedGraph V) (center : V) : LocalRegion V :=
  ⟨center, directedNeighborhood G center 2⟩

end LocalRegion

/-- A finite local complex with distinct source nodes, syndrome coordinates,
and correction coordinates. -/
structure LocalComplexData
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    where
  syndromeRegion : V → Finset SyndromeCoord
  correctionRegion : V → Finset CorrectionCoord

/-- The finite index type of one coordinate region. -/
abbrev LocalRegionIndex {Coord : Type v} (Y : Finset Coord) := {u : Coord // u ∈ Y}

/-- Restriction of a finite coordinate word to a region. -/
def restrictLocalSignal
    {Coord : Type v} {A : Type w} (Y : Finset Coord)
    (signal : Coord → A) : LocalRegionIndex Y → A :=
  fun u => signal u.1

/-- Zero extension of a local coordinate word to the full finite domain. -/
def extendLocalSignal
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (localSignal : LocalRegionIndex Y → A) : Coord → A :=
  fun u => if hu : u ∈ Y then localSignal ⟨u, hu⟩ else 0

/-- The pointwise mask used for ξ aggregation and restricted corrections. -/
def maskWord
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (signal : Coord → A) : Coord → A :=
  fun u => if u ∈ Y then signal u else 0

/-- A named zero-extension operation on coordinate words. -/
def zeroExtendWord
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (localSignal : LocalRegionIndex Y → A) : Coord → A :=
  extendLocalSignal Y localSignal

/-! ## Raw extension, support, and selected-map basis images

The selected-map part of the contract is deliberately basis-level.  It records
the finite image of each coordinate basis vector and support equations for
those images; it does not store an arbitrary word-level mask-commutation or
agreement oracle.
-/

structure ExtensionZeroLocalSupportImage
    {Owner : Type u} {Source : Type v} {Target : Type w}
    [Fintype Owner] [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (selectedMap : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target) where
  sourceRegion : Owner → Finset Source
  targetRegion : Owner → Finset Target
  extensionByZero : ∀ owner,
    Word BDL26Field (LocalRegionIndex (sourceRegion owner)) → Word BDL26Field Source
  extension_zero : ∀ owner localWord source,
    source ∉ sourceRegion owner → extensionByZero owner localWord source = 0
  extension_on_region :
    ∀ owner (localWord : Word BDL26Field (LocalRegionIndex (sourceRegion owner)))
      (source : LocalRegionIndex (sourceRegion owner)),
    extensionByZero owner localWord source.1 = localWord source
  selectedMapBasisImage : Source → Word BDL26Field Target
  selectedMap_basis_action : ∀ source,
    selectedMap (canonicalBasisWord source) = selectedMapBasisImage source
  selectedMap_basis_support : ∀ owner source target,
    source ∈ sourceRegion owner → target ∉ targetRegion owner →
      selectedMapBasisImage source target = 0
  selectedMap_basis_image : ∀ owner source target,
    source ∈ sourceRegion owner → selectedMapBasisImage source target ≠ 0 →
      target ∈ targetRegion owner

namespace ExtensionZeroLocalSupportImage

variable {Owner : Type u} {Source : Type v} {Target : Type w}
variable [Fintype Owner] [Fintype Source] [Fintype Target]
variable [DecidableEq Source] [DecidableEq Target]
variable {selectedMap : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target}

@[simp]
theorem extensionByZero_apply
    (A : ExtensionZeroLocalSupportImage selectedMap)
    (owner : Owner)
    (localWord : Word BDL26Field (LocalRegionIndex (A.sourceRegion owner)))
    (source : LocalRegionIndex (A.sourceRegion owner)) :
    A.extensionByZero owner localWord source.1 = localWord source :=
  A.extension_on_region owner localWord source

end ExtensionZeroLocalSupportImage

/-- Agreement of two finite coordinate words on an explicitly listed region. -/
def SignalsAgreeOn
    {Coord : Type v} {A : Type w}
    (Y : Finset Coord) (signal signal' : Coord → A) : Prop :=
  ∀ u, u ∈ Y → signal u = signal' u

namespace LocalComplexData

variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {A : Type y} [Zero A]

/-- Restrict a syndrome coordinate word at one centre. -/
def restrict (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (signal : SyndromeCoord → A) :
    LocalRegionIndex (L.syndromeRegion v) → A :=
  restrictLocalSignal (L.syndromeRegion v) signal

/-- Extend a local syndrome word back to the global domain. -/
def extend (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (localSignal : LocalRegionIndex (L.syndromeRegion v) → A) :
    SyndromeCoord → A :=
  extendLocalSignal (L.syndromeRegion v) localSignal

/-- Restrict a correction coordinate word at one centre. -/
def restrictCorrection (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (signal : CorrectionCoord → A) :
    LocalRegionIndex (L.correctionRegion v) → A :=
  restrictLocalSignal (L.correctionRegion v) signal

/-- Extend a local correction word back to the global domain. -/
def extendCorrection (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (localSignal : LocalRegionIndex (L.correctionRegion v) → A) :
    CorrectionCoord → A :=
  extendLocalSignal (L.correctionRegion v) localSignal

/-- The separate restriction/extension agreement predicate. -/
def RestrictExtendAgreement
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (signal : SyndromeCoord → A) : Prop :=
  ∀ v u, u ∈ L.syndromeRegion v → L.extend v (L.restrict v signal) u = signal u

end LocalComplexData

/-- Source nodes `u` contributing to `ξ_{i,v}(m)`, using directed `u → v`. -/
def xiIndexSet
    {V : Type v} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (v : V) (m : Nat) : Finset V :=
  LocalRegion.directedNeighborhood G v m

/-- The finite ξ aggregation over source nodes at directed distance at most `m`.

The aggregation is a pointwise sum of masked syndrome words.  The source
contract is interpreted as aggregating `σᵢ` after restriction to the source
region `Y_{v'}` (the displayed paper expression appears to use the target
subscript; this definition follows the audited local-complex meaning).
-/
def xiAggregate
    {V : Type v} [Fintype V] [DecidableEq V]
    {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    {A : Type y} [AddCommMonoid A]
    (G : DirectedGraph V)
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (sigma : SyndromeCoord → A) (v : V) (m : Nat) : SyndromeCoord → A :=
  fun z => Finset.sum (xiIndexSet G v m)
    (fun u => maskWord (L.syndromeRegion u) sigma z)

/-- Raw local correction components `f_{i,v}` and their finite total sum. -/
structure LocalCorrectionComponents
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    (Input : Type u) [Fintype Input]
    (Output : Type y) [Fintype Output] [AddCommMonoid Output]
    (L : LocalComplexData V SyndromeCoord CorrectionCoord) where
  component : ∀ _v : V, (SyndromeCoord → Input) → CorrectionCoord → Output

namespace LocalCorrectionComponents

variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {Input : Type u} [Fintype Input] [AddCommMonoid Input]
variable {Output : Type y} [Fintype Output] [AddCommMonoid Output]
variable {L : LocalComplexData V SyndromeCoord CorrectionCoord}

/-- The total correction is the finite sum of all local components. -/
def totalCorrection
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L)
    (sigma : SyndromeCoord → Input) : CorrectionCoord → Output :=
  fun z => Finset.sum Finset.univ (fun v => C.component v sigma z)

/-- The supplied decoder agrees with the component sum, as a separate Prop. -/
def TotalCorrectionDecomposition
    (decoder : (SyndromeCoord → Input) → CorrectionCoord → Output)
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ sigma, decoder sigma = C.totalCorrection sigma

/-- Every component is supported in its assigned `Y_v`. -/
def ComponentSupported
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma z, z ∉ L.correctionRegion v → C.component v sigma z = 0

/-- Masking the total correction at `v` recovers that component. -/
def MaskedTotalCorrectionEqComponent
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma,
    maskWord (L.correctionRegion v) (C.totalCorrection sigma) = C.component v sigma

/-- Component equality after the source radius-one ξ restriction. -/
def ComponentInvariantAtXiOne
    (G : DirectedGraph V)
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma,
    C.component v sigma = C.component v (xiAggregate G L sigma v 1)

/-- Every coarse coordinate is invariant after its radius-two ξ restriction. -/
def CoarseCoordinateInvariantAtXiTwo
    {CoarseCoord : Type a}
    (G : DirectedGraph V)
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (coarse : (SyndromeCoord → Input) → CoarseCoord → Output)
    (centerOf : CoarseCoord → V) : Prop :=
  ∀ z sigma,
    coarse sigma z = coarse (xiAggregate G L sigma (centerOf z) 2) z

end LocalCorrectionComponents

/-- A level graph together with the X→Q→Z orientation used for directed
distance.  The `kind` labelling is deliberately an interface, not a concrete
construction instance; M13 discharges the corresponding BDL26 contract. -/
structure LevelGraph (V : Type v) [Fintype V] [DecidableEq V] where
  /-- The undirected Tanner skeleton supplied by the locality layer. -/
  skeleton : Locality.ConnectivityGraph V
  kind : V → LevelVertexKind
  skeletonDecidable : ∀ u v, Decidable (skeleton.adjacent u v)

namespace LevelGraph

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The executable directed edge adapter derived from skeleton adjacency and labels. -/
def directedEdge (L : LevelGraph V) (u v : V) : Bool :=
  letI : Decidable (L.skeleton.adjacent u v) := L.skeletonDecidable u v
  let adjacency : Bool := decide (L.skeleton.adjacent u v)
  let xq : Bool := decide (L.kind u = .x) && decide (L.kind v = .q)
  let qz : Bool := decide (L.kind u = .q) && decide (L.kind v = .z)
  adjacency && (xq || qz)

/-- The oriented graph is derived from the skeleton; it cannot drift independently. -/
def graph (L : LevelGraph V) : DirectedGraph V where
  edge := L.directedEdge
  loopless := by
    intro u
    letI : Decidable (L.skeleton.adjacent u u) := L.skeletonDecidable u u
    simp [directedEdge, L.skeleton.loopless u]

@[simp]
theorem directedEdge_orientation (L : LevelGraph V) (u v : V)
    (h : L.graph.edge u v = true) :
    (L.kind u = .x ∧ L.kind v = .q) ∨
      (L.kind u = .q ∧ L.kind v = .z) := by
  simp only [graph, directedEdge] at h
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true,
    Bool.or_eq_true_eq_eq_true_or_eq_true] at h
  rcases h.2 with hXQ | hQZ
  · exact Or.inl ⟨of_decide_eq_true hXQ.1, of_decide_eq_true hXQ.2⟩
  · exact Or.inr ⟨of_decide_eq_true hQZ.1, of_decide_eq_true hQZ.2⟩

end LevelGraph

/-- The exact undirected-skeleton/directed-edge compatibility contract. -/
def LevelGraphSkeletonCoherence
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V) : Prop :=
  ∀ u v, L.skeleton.adjacent u v ↔
    L.graph.edge u v = true ∨ L.graph.edge v u = true

/-- The directed Tanner orientation contract `X → Q → Z`. -/
def LevelGraphDirectedOrientation
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V) : Prop :=
  ∀ u v, L.graph.edge u v = true →
    (L.kind u = .x ∧ L.kind v = .q) ∨
      (L.kind u = .q ∧ L.kind v = .z)

/-- Per-kind equivalences exposed to the concrete M13 realization. -/
structure LevelGraphVertexEquivalence
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V)
    (X Q Z : Type w) where
  xEquiv : {u : V // L.kind u = .x} ≃ X
  qEquiv : {u : V // L.kind u = .q} ≃ Q
  zEquiv : {u : V // L.kind u = .z} ≃ Z

/-- An exact graph-isomorphism predicate for an external Tanner skeleton. -/
def LevelGraphSkeletonIsomorphism
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (T : Locality.ConnectivityGraph W) (e : W ≃ V) : Prop :=
  ∀ a b, T.adjacent a b ↔ L.skeleton.adjacent (e a) (e b)

/-- Exact preservation of the X/Q/Z vertex labelling under the same equivalence. -/
def LevelGraphLabelPreservation
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (label : W → LevelVertexKind) (e : W ≃ V) : Prop :=
  ∀ a, L.kind (e a) = label a

/-- The combined Tanner skeleton/label equivalence exposed to M13. -/
def LevelGraphTannerIsomorphism
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (T : Locality.ConnectivityGraph W)
    (label : W → LevelVertexKind) (e : W ≃ V) : Prop :=
  LevelGraphSkeletonIsomorphism L T e ∧ LevelGraphLabelPreservation L label e

/-- A finite family of level graphs and consecutive-level incidence edges. -/
structure DecodingGraphFamily
    (depth : Nat)
    (V : LevelIndex depth → Type v)
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] where
  level : ∀ i : LevelIndex depth, LevelGraph (V i)
  interLevel : ∀ i : StepIndex depth, V i.castSucc → V i.succ → Bool
  root : V (0 : LevelIndex depth)
  root_unique : ∀ v : V (0 : LevelIndex depth), v = root

namespace DecodingGraphFamily

variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- Nodes of the level-union decoding graph. -/
abbrev Node (_G : DecodingGraphFamily depth V) := Σ i : LevelIndex depth, V i

/-- The undirected union relation in the level-union decoding graph.

Each oriented level edge is admitted in both directions in this union;
consecutive-level incidence is likewise admitted in both orientations.  The
root-to-level-one convention is the `interLevel` relation at the zero step,
whose source is the unique root. -/
def adjacent (G : DecodingGraphFamily depth V) (u v : G.Node) : Prop :=
  match u, v with
  | ⟨i, x⟩, ⟨j, y⟩ =>
      (if h : i = j then
          (G.level i).skeleton.adjacent x (h ▸ y)
        else False) ∨
      (∃ s : StepIndex depth,
        if h0 : i = s.castSucc then
          if h1 : j = s.succ then G.interLevel s (h0 ▸ x) (h1 ▸ y) = true
          else False
        else False) ∨
      (∃ s : StepIndex depth,
        if h0 : j = s.castSucc then
          if h1 : i = s.succ then G.interLevel s (h0 ▸ y) (h1 ▸ x) = true
          else False
        else False)

/-- The directed level distance used by local-computability predicates. -/
def levelDistance
    (G : DecodingGraphFamily depth V)
    (i : LevelIndex depth) (u v : V i) : WithTop Nat :=
  DirectedGraph.distance (G.level i).graph u v

/-- The source root-incidence requirement for a nonempty level one. -/
def RootConnectedToLevelOne
    (G : DecodingGraphFamily depth V) (hdepth : 0 < depth) : Prop :=
  ∀ v : V ⟨1, Nat.lt_succ_of_le hdepth⟩,
    G.interLevel ⟨0, hdepth⟩ G.root v = true

/-- An exact, externally supplied specification of every inter-level edge. -/
def ExactInterLevelIncidence
    (G : DecodingGraphFamily depth V)
    (expected : ∀ i : StepIndex depth, V i.castSucc → V i.succ → Bool) : Prop :=
  ∀ i x y, G.interLevel i x y = expected i x y

end DecodingGraphFamily

/-- The level-two index, available under the finite depth contract `2 ≤ depth`. -/
def levelTwoIndex {depth : Nat} (hdepth : 2 ≤ depth) : LevelIndex depth :=
  ⟨2, Nat.lt_succ_of_le hdepth⟩

def levelOneIndex {depth : Nat} (hdepth : 1 ≤ depth) : LevelIndex depth :=
  ⟨1, Nat.lt_succ_of_le hdepth⟩

def levelOneStep {depth : Nat} (hdepth : 2 ≤ depth) : StepIndex depth :=
  ⟨1, Nat.lt_of_lt_of_le (by decide) hdepth⟩

/-! ## Raw adjacent-level owners and incidence

Owner labels are partial on purpose: a `none` owner is the explicit raw
representation of a connector, zero, or otherwise unowned coordinate.  The
membership guards below are exact finite equalities; they do not assert a
component, transport, or locality conclusion.
-/

structure AdjacentLevelOwnerIncidence
    (depth : Nat)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (SyndromeCoord : LevelIndex depth → Type w)
    [∀ i, Fintype (SyndromeCoord i)] [∀ i, DecidableEq (SyndromeCoord i)]
    (CorrectionCoord : LevelIndex depth → Type x)
    [∀ i, Fintype (CorrectionCoord i)]
    [∀ i, DecidableEq (CorrectionCoord i)]
    (G : DecodingGraphFamily depth V) where
  syndromeOwner : ∀ i, SyndromeCoord i → Option (V i)
  correctionOwner : ∀ i, CorrectionCoord i → Option (V i)
  syndromeRegion : ∀ i, V i → Finset (SyndromeCoord i)
  correctionRegion : ∀ i, V i → Finset (CorrectionCoord i)
  syndromeOwner_mem_iff : ∀ i v c,
    syndromeOwner i c = some v ↔ c ∈ syndromeRegion i v
  correctionOwner_mem_iff : ∀ i v c,
    correctionOwner i c = some v ↔ c ∈ correctionRegion i v
  syndromeOwner_none_iff : ∀ i c,
    syndromeOwner i c = none ↔ ∀ v, c ∉ syndromeRegion i v
  correctionOwner_none_iff : ∀ i c,
    correctionOwner i c = none ↔ ∀ v, c ∉ correctionRegion i v
  parentIncidence : ∀ i : StepIndex depth, V i.succ → Option (V i.castSucc)
  parentIncidence_mem_iff : ∀ i u v,
    parentIncidence i v = some u ↔ G.interLevel i u v = true
  root_parent_incidence : ∀ (hdepth : 1 ≤ depth)
    (v : V (levelOneIndex hdepth)),
    parentIncidence ⟨0, hdepth⟩ v = some G.root

/-! This optional parent map intentionally does not impose totality at level two:
connector or unowned coordinates may remain `none`; concrete nonempty incidence
is supplied by the project-derived family data and checked by later issues. -/

/-- Machine-readable schema name for the additive raw geometry surface. -/
def bdl26RawGeometryAddendumSchemaVersion : String :=
  "bdl26-raw-cross-level-geometry-v1"

namespace AdjacentLevelOwnerIncidence

variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}

theorem syndrome_mem_of_owner
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (c : SyndromeCoord i) (v : V i)
    (h : A.syndromeOwner i c = some v) :
    c ∈ A.syndromeRegion i v :=
  (A.syndromeOwner_mem_iff i v c).mp h

theorem correction_mem_of_owner
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (c : CorrectionCoord i) (v : V i)
    (h : A.correctionOwner i c = some v) :
    c ∈ A.correctionRegion i v :=
  (A.correctionOwner_mem_iff i v c).mp h

theorem parent_mem_of_incidence
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : StepIndex depth) (u : V i.castSucc) (v : V i.succ)
    (h : A.parentIncidence i v = some u) :
    G.interLevel i u v = true :=
  (A.parentIncidence_mem_iff i u v).mp h

end AdjacentLevelOwnerIncidence

namespace AdjacentLevelOwnerIncidence

variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}

/-- Adapter into the existing M12 local-region API. -/
def toLocalComplexData
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) :
    LocalComplexData (V i) (SyndromeCoord i) (CorrectionCoord i) where
  syndromeRegion := A.syndromeRegion i
  correctionRegion := A.correctionRegion i

@[simp]
theorem toLocalComplexData_syndromeRegion
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (v : V i) :
    (A.toLocalComplexData i).syndromeRegion v = A.syndromeRegion i v :=
  rfl

@[simp]
theorem toLocalComplexData_correctionRegion
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (v : V i) :
    (A.toLocalComplexData i).correctionRegion v = A.correctionRegion i v :=
  rfl

end AdjacentLevelOwnerIncidence

/-! ## The versioned raw cross-level geometry bundle -/

structure RawCrossLevelGeometry
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : DecodingGraphFamily depth V) where
  basisActions : ∀ i : StepIndex depth, TypedCoordinateBasisActions D i
  ownerIncidence :
    AdjacentLevelOwnerIncidence depth V C2 C1 G
  rxDegreeOne : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C1 i.castSucc) (Target := C1 i.succ)
      (D.rxMap i).map1
  rxDegreeTwo : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C2 i.castSucc) (Target := C2 i.succ)
      (D.rxMap i).map2
  rzDegreeOne : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C1 i.castSucc) (Target := C1 i.succ)
      (D.rzMap i).map1
  rzDegreeTwo : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C2 i.castSucc) (Target := C2 i.succ)
      (D.rzMap i).map2

/-! Versioned name used by the M13 addendum.  This is an additive alias over
the raw record; the closed #809 `BDL26DecoderData` fields are untouched. -/
abbrev BDL26RawGeometryAddendumV1
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : DecodingGraphFamily depth V) :=
  RawCrossLevelGeometry D V G

namespace RawCrossLevelGeometry

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)] [∀ i, DecidableEq (C1 i)]
  [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {G : DecodingGraphFamily depth V}

/-! The graph is an explicit parameter in the record above through the
owner-incidence field; the following adapters expose the existing M12 APIs
without adding any conclusion-bearing field to the raw bundle. -/

def localComplexData
    (A : RawCrossLevelGeometry D V G)
    (i : LevelIndex depth) :
    LocalComplexData (V i) (C2 i) (C1 i) :=
  A.ownerIncidence.toLocalComplexData i

def selectedCochainMap
    (_A : RawCrossLevelGeometry D V G) (i : StepIndex depth) :
    BDL26CochainMap D.family i :=
  D.selectedMap i

end RawCrossLevelGeometry

/-- The #809 stability-facing level-two input surface.

It records only a finite syndrome and the centre whose exact radius-two region
is consumed by a later base decoder.  It does not assert that any error is
corrected. -/
structure StabilityBaseLevelTwoInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  syndrome : D.family.Syndrome (levelTwoIndex hdepth)
  center : V (levelTwoIndex hdepth)
  syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)

namespace StabilityBaseLevelTwoInput

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}

/-- The exact source radius-two region for the recorded centre. -/
def region
    (I : StabilityBaseLevelTwoInput D G hdepth) : LocalRegion (V (levelTwoIndex hdepth)) :=
  LocalRegion.syndromeRegion (G.level (levelTwoIndex hdepth)).graph I.center

/-- The separately checked support-to-ball condition for the level-two input. -/
def supportFitsRadiusTwo
    (I : StabilityBaseLevelTwoInput D G hdepth) : Prop :=
  ∀ c, c ∈ D.family.syndromeSupport (levelTwoIndex hdepth) I.syndrome →
    I.syndromeLocation c ∈ (I.region).vertices

end StabilityBaseLevelTwoInput

/-- The raw level-two decoder map from F17.  Recursive level zero is represented
by `RecursiveBaseLevelCorrection` above and is intentionally a separate type. -/
abbrev BaseLevelTwoDecoder
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (_G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) :=
  D.family.Syndrome (levelTwoIndex hdepth) →
    D.family.Correction (levelTwoIndex hdepth)

/-- F17's unconditional level-two right-inverse condition. -/
def BaseLevelTwoDecoderIsRightInverse
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ sigma, D.family.coboundary1 (levelTwoIndex hdepth) (decode sigma) =
    (sigma : D.family.Cochain2 (levelTwoIndex hdepth))

/-- A separate small-error interface: for an actual error whose syndrome is the
recorded input and whose support fits the radius-two ball, the residual error
is in the existing first-coboundary check-code carrier. -/
def BaseLevelTwoDecoderSmallError
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ (I : StabilityBaseLevelTwoInput D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth)),
    I.supportFitsRadiusTwo →
      (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
        D.family.coboundary1 (levelTwoIndex hdepth) error →
      error + decode I.syndrome ∈
        (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier

/-! ## Version-two F17 actual-error-local contract

The declarations above are the historical #809/#815 surface.  In particular,
`BaseLevelTwoDecoderSmallError` remains available with its original meaning for
provenance.  Concrete F17 consumers use the version-two declarations below,
whose domain is the support of the actual error rather than the support of its
syndrome.
-/

/-- Machine-readable schema name for the repaired F17 small-error surface. -/
def f17LevelTwoSmallErrorContractVersion : String :=
  "bdl26-f17-actual-error-local-v2"

/-- An error is local when its actual Hamming support lies in one concrete
level-two correction region.  This predicate says nothing about the error's
syndrome or logical class. -/
noncomputable def LevelTwoLocalError
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (hdepth : 2 ≤ depth)
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (error : D.family.Correction (levelTwoIndex hdepth)) : Prop := by
  classical
  exact ∃ center, hammingSupport error ⊆ L.correctionRegion center

/-- Pure data for one version-two F17 query.  Locality and correctness are
separate named propositions, not fields of this record. -/
structure LevelTwoSmallErrorInputV2
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (hdepth : 2 ≤ depth) where
  error : D.family.Correction (levelTwoIndex hdepth)

namespace LevelTwoSmallErrorInputV2

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {hdepth : 2 ≤ depth}

/-- The syndrome presented to a decoder is derived from the actual error. -/
noncomputable def syndrome (I : LevelTwoSmallErrorInputV2 D hdepth) :
    D.family.Syndrome (levelTwoIndex hdepth) :=
  ⟨D.family.coboundary1 (levelTwoIndex hdepth) I.error,
    ⟨I.error, rfl⟩⟩

@[simp] theorem coe_syndrome
    (I : LevelTwoSmallErrorInputV2 D hdepth) :
    (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
      D.family.coboundary1 (levelTwoIndex hdepth) I.error :=
  rfl

/-- The separately checked version-two domain guard. -/
noncomputable def IsLocal
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (I : LevelTwoSmallErrorInputV2 D hdepth) : Prop :=
  LevelTwoLocalError D hdepth L I.error

end LevelTwoSmallErrorInputV2

/-- The repaired F17 small-error property.  It is a proposition about a
decoder, not a field supplied by construction data or an adapter. -/
noncomputable def BaseLevelTwoDecoderSmallErrorV2
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ I : LevelTwoSmallErrorInputV2 D hdepth,
    I.IsLocal L →
      I.error + decode I.syndrome ∈
        (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier

/-- A zero-syndrome historical input.  It is used only to expose why the v1
syndrome-support guard cannot be a concrete correctness domain. -/
def historicalZeroSyndromeInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)) :
    StabilityBaseLevelTwoInput D G hdepth where
  syndrome := ⟨0, by simp [BDL26CochainFamily.syndromeSubmodule]⟩
  center := center
  syndromeLocation := syndromeLocation

@[simp] theorem historicalZeroSyndromeInput_supportFitsRadiusTwo
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)) :
    (historicalZeroSyndromeInput D G hdepth center syndromeLocation).supportFitsRadiusTwo := by
  classical
  intro coordinate hcoordinate
  simp [historicalZeroSyndromeInput, BDL26CochainFamily.syndromeSupport,
    hammingSupport] at hcoordinate

/-- Zero-syndrome regression: if level two has a cocycle outside the first
coboundaries, the historical syndrome-support-only universal predicate is
false for every decoder.  The proof needs no assumption about `decode 0`: the
old predicate applied to the zero error first forces `decode 0` to be a
coboundary, and applying it to the logical cocycle gives the contradiction. -/
theorem not_baseLevelTwoDecoderSmallError_of_nontrivial_cocycle
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth))
    (decode : BaseLevelTwoDecoder D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth))
    (hCocycle : D.family.coboundary1 (levelTwoIndex hdepth) error = 0)
    (hNontrivial : error ∉
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier) :
    ¬ BaseLevelTwoDecoderSmallError D G hdepth decode := by
  intro hOld
  let I := historicalZeroSyndromeInput D G hdepth center syndromeLocation
  have hFits : I.supportFitsRadiusTwo := by
    exact historicalZeroSyndromeInput_supportFitsRadiusTwo
      D G hdepth center syndromeLocation
  have hZeroSyndrome :
      (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
        D.family.coboundary1 (levelTwoIndex hdepth) 0 := by
    simp [I, historicalZeroSyndromeInput]
  have hDecode :
      (0 : D.family.Correction (levelTwoIndex hdepth)) + decode I.syndrome ∈
        (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier :=
    hOld I 0 hFits hZeroSyndrome
  have hErrorSyndrome :
      (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
        D.family.coboundary1 (levelTwoIndex hdepth) error := by
    simpa [I, historicalZeroSyndromeInput] using hCocycle.symm
  have hResidual := hOld I error hFits hErrorSyndrome
  have hDecodeMem : decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier := by
    simpa using hDecode
  have hSum :=
    (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier.add_mem
      hResidual hDecodeMem
  have hCancel :
      (error + decode I.syndrome) + decode I.syndrome = error := by
    ext coordinate
    simp [add_assoc, CharTwo.add_self_eq_zero]
  rw [hCancel] at hSum
  exact hNontrivial hSum


/-- Generic radius extensionality for a finite graph signal.

This is a reusable comparison predicate only; the BDL26 source-exact claims
are the separate ξ predicates above. -/
def RadiusExtensionalityAt
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V) (radius : Nat)
    (outputAt : (V → Input) → V → Output) : Prop :=
  ∀ v : V, ∀ input input' : V → Input,
    (∀ u, u ∈ LocalRegion.directedNeighborhood G v radius → input u = input' u) →
      outputAt input v = outputAt input' v

/-- Generic radius-one extensionality for a correction-valued function. -/
def CorrectionRadiusExtensionality
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V)
    (correctionAt : (V → Input) → V → Output) : Prop :=
  RadiusExtensionalityAt G 1 correctionAt

/-- Generic radius-two extensionality for a coarse-syndrome-valued function. -/
def CoarseSyndromeRadiusExtensionality
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V)
    (syndromeAt : (V → Input) → V → Output) : Prop :=
  RadiusExtensionalityAt G 2 syndromeAt

/-- Raw source-exact local decoder data for one finite coarse-graining level.

The record stores only the global correction decoder, its local component
family, the coarse-syndrome decoder, and the centre map for coarse coordinates.
All five source-exact locality/decomposition statements below remain separate
Props; no proof field is stored here. -/
structure LocalComputabilityInterface
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    (CoarseCoord : Type u) [Fintype CoarseCoord] [DecidableEq CoarseCoord]
    (Input : Type y) [Fintype Input] [AddCommMonoid Input]
    (Output : Type z) [Fintype Output] [AddCommMonoid Output]
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (G : DirectedGraph V) where
  correction : (SyndromeCoord → Input) → CorrectionCoord → Output
  components : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L
  coarseSyndrome : (SyndromeCoord → Input) → CoarseCoord → Output
  coarseCenter : CoarseCoord → V

namespace LocalComputabilityInterface

variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {CoarseCoord : Type u} [Fintype CoarseCoord] [DecidableEq CoarseCoord]
variable {Input : Type y} [Fintype Input] [AddCommMonoid Input]
variable {Output : Type z} [Fintype Output] [AddCommMonoid Output]
variable {L : LocalComplexData V SyndromeCoord CorrectionCoord}
variable {G : DirectedGraph V}

/-- The global correction equals the finite sum of local components. -/
def totalCorrectionDecomposition
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.TotalCorrectionDecomposition I.correction I.components

/-- Every local component is supported in its correction region. -/
def componentSupported
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.ComponentSupported I.components

/-- Masking the total correction at a centre recovers that component. -/
def maskedTotalCorrectionEqComponent
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.MaskedTotalCorrectionEqComponent I.components

/-- Components are invariant after the source radius-one ξ restriction. -/
def componentInvariantAtXiOne
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.ComponentInvariantAtXiOne G I.components

/-- Each coarse coordinate is invariant after its source radius-two ξ restriction. -/
def coarseCoordinateInvariantAtXiTwo
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.CoarseCoordinateInvariantAtXiTwo
    (Input := Input) (Output := Output) (CoarseCoord := CoarseCoord)
    G L I.coarseSyndrome I.coarseCenter

end LocalComputabilityInterface

end MultiscaleDecoder
end Coding
end QEC
