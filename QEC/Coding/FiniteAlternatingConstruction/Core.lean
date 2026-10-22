import QEC.Coding.FourDimensionalToricCode.Decoder.Multiscale
import Mathlib.LinearAlgebra.StdBasis

/-!
# Finite alternating construction core for BDL26

This module supplies the finite BDL26 construction core:
the concrete `2 -> 5 -> 2` seed, its Tanner graph and coordinate bases, and a
finite parity-typed carrier recursion.  The displayed seed matrices encode the
incidence in the source's `Tanner-base.png` under the explicit project
coordinate numbering recorded by the bounded seed-mapping audit record
`bdl26-finite-seed-coordinate-mapping-v1`.

The recursion below constructs only finite coordinate carriers.  Only the base
seed has actual coboundaries in this module; successor coboundaries and their
well-formedness proofs belong to the replacement constructions.  No decoder,
transport, logical, embedding, or lifetime conclusion appears here.
-/

namespace QEC
namespace Coding
namespace BDL26FiniteAlternatingCore

open MultiscaleDecoder
open Module

abbrev Field := BDL26Field
abbrev BaseX := Fin 2
abbrev BaseQubit := Fin 5
abbrev BaseZ := Fin 2

/-! ## Concrete finite seed -/

/-- The two-by-five first boundary of the source-depicted finite seed. -/
def baseBoundary1Matrix : Matrix BaseX BaseQubit Field :=
  !![1, 1, 0, 0, 1;
     0, 0, 1, 1, 1]

/-- The five-by-two second boundary of the source-depicted finite seed. -/
def baseBoundary2Matrix : Matrix BaseQubit BaseZ Field :=
  !![1, 0;
     0, 1;
     1, 0;
     0, 1;
     1, 1]

/-- Every X/Z incidence pair overlaps evenly in the concrete seed. -/
theorem baseBoundaryMatrices_mul :
    baseBoundary1Matrix * baseBoundary2Matrix = 0 := by
  decide

/-- The first boundary as a finite-coordinate linear map. -/
noncomputable def baseBoundary1 :
    Word Field BaseQubit →ₗ[Field] Word Field BaseX :=
  Matrix.toLin' baseBoundary1Matrix

/-- The second boundary as a finite-coordinate linear map. -/
noncomputable def baseBoundary2 :
    Word Field BaseZ →ₗ[Field] Word Field BaseQubit :=
  Matrix.toLin' baseBoundary2Matrix

/-- The concrete seed is a well-formed three-term chain complex. -/
theorem baseBoundary_squared : baseBoundary1.comp baseBoundary2 = 0 := by
  change (Matrix.toLin' baseBoundary1Matrix).comp
    (Matrix.toLin' baseBoundary2Matrix) = 0
  rw [← Matrix.toLin'_mul, baseBoundaryMatrices_mul]
  simp

/-- The concrete finite `C_(0) : F_2^2 -> F_2^5 -> F_2^2` seed. -/
noncomputable def baseChainComplex :
    ChainComplexData Field
      (Word Field BaseX) (Word Field BaseQubit) (Word Field BaseZ) where
  boundary1 := baseBoundary1
  boundary2 := baseBoundary2
  boundary_squared := baseBoundary_squared

/-- The canonical finite basis of the seed's degree-zero carrier. -/
noncomputable def baseXBasis : Basis BaseX Field (Word Field BaseX) :=
  Pi.basisFun Field BaseX

/-- The canonical finite basis of the seed's degree-one carrier. -/
noncomputable def baseQubitBasis : Basis BaseQubit Field (Word Field BaseQubit) :=
  Pi.basisFun Field BaseQubit

/-- The canonical finite basis of the seed's degree-two carrier. -/
noncomputable def baseZBasis : Basis BaseZ Field (Word Field BaseZ) :=
  Pi.basisFun Field BaseZ

@[simp]
theorem baseX_card : Fintype.card BaseX = 2 := by simp [BaseX]

@[simp]
theorem baseQubit_card : Fintype.card BaseQubit = 5 := by simp [BaseQubit]

@[simp]
theorem baseZ_card : Fintype.card BaseZ = 2 := by simp [BaseZ]

@[simp]
theorem baseXBasis_apply (x y : BaseX) :
    baseXBasis x y = if x = y then 1 else 0 := by
  classical
  rw [baseXBasis, Pi.basisFun_apply]
  by_cases h : x = y
  · subst y
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]

@[simp]
theorem baseQubitBasis_apply (q r : BaseQubit) :
    baseQubitBasis q r = if q = r then 1 else 0 := by
  classical
  rw [baseQubitBasis, Pi.basisFun_apply]
  by_cases h : q = r
  · subst r
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]

@[simp]
theorem baseZBasis_apply (z w : BaseZ) :
    baseZBasis z w = if z = w then 1 else 0 := by
  classical
  rw [baseZBasis, Pi.basisFun_apply]
  by_cases h : z = w
  · subst w
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]

/-! ## Tanner seed -/

/-- The three typed vertex classes of the finite seed Tanner graph. -/
inductive BaseTannerVertex where
  | x : BaseX → BaseTannerVertex
  | q : BaseQubit → BaseTannerVertex
  | z : BaseZ → BaseTannerVertex
  deriving DecidableEq, Fintype

/-- The role of each concrete seed vertex. -/
def baseTannerKind : BaseTannerVertex → LevelVertexKind
  | .x _ => .x
  | .q _ => .q
  | .z _ => .z

/-- Undirected Tanner adjacency derived from the two concrete boundaries. -/
def baseTannerAdjacent : BaseTannerVertex → BaseTannerVertex → Prop
  | .x x, .q q => baseBoundary1Matrix x q ≠ 0
  | .q q, .x x => baseBoundary1Matrix x q ≠ 0
  | .q q, .z z => baseBoundary2Matrix q z ≠ 0
  | .z z, .q q => baseBoundary2Matrix q z ≠ 0
  | _, _ => False

instance baseTannerAdjacentDecidable (u v : BaseTannerVertex) :
    Decidable (baseTannerAdjacent u v) := by
  cases u <;> cases v <;> unfold baseTannerAdjacent <;> infer_instance

/-- The concrete finite Tanner skeleton of the source-depicted seed. -/
def baseTannerSkeleton : Locality.ConnectivityGraph BaseTannerVertex where
  adjacent := baseTannerAdjacent
  symmetric := by
    intro u v h
    cases u <;> cases v <;> exact h
  loopless := by
    intro u
    cases u <;> simp [baseTannerAdjacent]

/-- The concrete seed as the project-wide labelled level graph. -/
def baseLevelGraph : LevelGraph BaseTannerVertex where
  skeleton := baseTannerSkeleton
  kind := baseTannerKind
  skeletonDecidable := baseTannerAdjacentDecidable

@[simp]
theorem baseTanner_xq_adjacent (x : BaseX) (q : BaseQubit) :
    baseLevelGraph.skeleton.adjacent (.x x) (.q q) ↔
      baseBoundary1Matrix x q ≠ 0 :=
  Iff.rfl

@[simp]
theorem baseTanner_qx_adjacent (q : BaseQubit) (x : BaseX) :
    baseLevelGraph.skeleton.adjacent (.q q) (.x x) ↔
      baseBoundary1Matrix x q ≠ 0 :=
  Iff.rfl

@[simp]
theorem baseTanner_qz_adjacent (q : BaseQubit) (z : BaseZ) :
    baseLevelGraph.skeleton.adjacent (.q q) (.z z) ↔
      baseBoundary2Matrix q z ≠ 0 :=
  Iff.rfl

@[simp]
theorem baseTanner_zq_adjacent (z : BaseZ) (q : BaseQubit) :
    baseLevelGraph.skeleton.adjacent (.z z) (.q q) ↔
      baseBoundary2Matrix q z ≠ 0 :=
  Iff.rfl

theorem baseTanner_typed_adjacency {u v : BaseTannerVertex}
    (h : baseLevelGraph.skeleton.adjacent u v) :
    (baseTannerKind u = .x ∧ baseTannerKind v = .q) ∨
      (baseTannerKind u = .q ∧ baseTannerKind v = .x) ∨
      (baseTannerKind u = .q ∧ baseTannerKind v = .z) ∨
      (baseTannerKind u = .z ∧ baseTannerKind v = .q) := by
  cases u <;> cases v <;> simp_all [baseLevelGraph, baseTannerSkeleton,
    baseTannerAdjacent, baseTannerKind]

@[simp]
theorem baseLevelGraph_xq_directed (x : BaseX) (q : BaseQubit) :
    baseLevelGraph.graph.edge (.x x) (.q q) = true ↔
      baseBoundary1Matrix x q ≠ 0 := by
  simp [LevelGraph.graph, LevelGraph.directedEdge, baseLevelGraph,
    baseTannerSkeleton, baseTannerAdjacent, baseTannerKind]
  exact decide_eq_true_iff

@[simp]
theorem baseLevelGraph_qz_directed (q : BaseQubit) (z : BaseZ) :
    baseLevelGraph.graph.edge (.q q) (.z z) = true ↔
      baseBoundary2Matrix q z ≠ 0 := by
  simp [LevelGraph.graph, LevelGraph.directedEdge, baseLevelGraph,
    baseTannerSkeleton, baseTannerAdjacent, baseTannerKind]
  exact decide_eq_true_iff

/-- The concrete undirected skeleton is exactly the symmetrization of the
typed `X -> Q -> Z` orientation. -/
theorem baseLevelGraph_skeleton_coherence :
    LevelGraphSkeletonCoherence baseLevelGraph := by
  intro u v
  cases u <;> cases v <;>
    simp [LevelGraph.graph, LevelGraph.directedEdge, baseLevelGraph,
      baseTannerSkeleton, baseTannerAdjacent, baseTannerKind] <;>
      exact decide_eq_true_iff.symm

/-! ## Raw finite cochain carriers -/

/-- One finite three-term coordinate carrier.

This package deliberately contains neither coboundary maps nor a
well-formedness proof.  The RX and RZ construction branches must build and
prove those maps rather than receive them from a caller.
-/
structure FiniteCochainCarrier where
  C0 : Type
  C1 : Type
  C2 : Type
  fintypeC0 : Fintype C0
  fintypeC1 : Fintype C1
  fintypeC2 : Fintype C2

attribute [instance] FiniteCochainCarrier.fintypeC0
attribute [instance] FiniteCochainCarrier.fintypeC1
attribute [instance] FiniteCochainCarrier.fintypeC2

/-- The concrete seed packaged as a recursion carrier. -/
def baseCarrier : FiniteCochainCarrier where
  C0 := BaseX
  C1 := BaseQubit
  C2 := BaseZ
  fintypeC0 := inferInstance
  fintypeC1 := inferInstance
  fintypeC2 := inferInstance

/-- The type of a degree-zero coboundary on a raw carrier. -/
abbrev Coboundary0 (L : FiniteCochainCarrier) :=
  Word Field L.C0 →ₗ[Field] Word Field L.C1

/-- The type of a degree-one coboundary on a raw carrier. -/
abbrev Coboundary1 (L : FiniteCochainCarrier) :=
  Word Field L.C1 →ₗ[Field] Word Field L.C2

/-- The actual degree-zero coboundary of the concrete base seed. -/
noncomputable def baseCoboundary0 : Coboundary0 baseCarrier :=
  wordLinearMapTranspose baseBoundary1

/-- The actual degree-one coboundary of the concrete base seed. -/
noncomputable def baseCoboundary1 : Coboundary1 baseCarrier :=
  wordLinearMapTranspose baseBoundary2

/-- The concrete base coboundaries compose to zero. -/
theorem baseCoboundary_squared :
    baseCoboundary1.comp baseCoboundary0 = 0 := by
  change (wordLinearMapTranspose baseBoundary2).comp
    (wordLinearMapTranspose baseBoundary1) = 0
  rw [← wordLinearMapTranspose_comp, baseBoundary_squared]
  apply LinearMap.ext
  intro word
  ext coordinate
  simp [wordLinearMapTranspose]

/-! ## Finite parity-typed recursion -/

/-- A forward step at an even source level. -/
abbrev EvenStep := {i : Nat // i % 2 = 0}

/-- A forward step at an odd source level. -/
abbrev OddStep := {i : Nat // i % 2 = 1}

/-- The canonical RX source step `2i`. -/
def rxStep (i : Nat) : EvenStep := ⟨2 * i, by omega⟩

/-- The canonical RZ source step `2i+1`. -/
def rzStep (i : Nat) : OddStep := ⟨2 * i + 1, by omega⟩

@[simp]
theorem rxStep_val (i : Nat) : (rxStep i).1 = 2 * i := rfl

@[simp]
theorem rzStep_val (i : Nat) : (rzStep i).1 = 2 * i + 1 := rfl

/-- Eliminate an arbitrary step into its even RX or odd RZ branch. -/
theorem even_or_odd_step (i : Nat) : i % 2 = 0 ∨ i % 2 = 1 := by
  omega

/-- The parity selector names RX exactly at even source levels. -/
theorem replacementKind_eq_rx_iff (i : Nat) :
    replacementKind i = .rx ↔ i % 2 = 0 := by
  simp [replacementKind]

/-- The parity selector names RZ exactly at odd source levels. -/
theorem replacementKind_eq_rz_iff (i : Nat) :
    replacementKind i = .rz ↔ i % 2 = 1 := by
  rw [replacementKind]
  split <;> simp_all

@[simp]
theorem replacementKind_rxStep (i : Nat) :
    replacementKind (rxStep i).1 = .rx := by
  simp [replacementKind, rxStep]

@[simp]
theorem replacementKind_rzStep (i : Nat) :
    replacementKind (rzStep i).1 = .rz := by
  simp [replacementKind, rzStep]

/-- Raw carrier constructors supplied separately by the RX and RZ branches.

These functions return only the next finite coordinate carrier.  They contain
no coboundary, replacement map, or preservation proof.
-/
structure AlternatingCarrierConstructors where
  rx : EvenStep → FiniteCochainCarrier → FiniteCochainCarrier
  rz : OddStep → FiniteCochainCarrier → FiniteCochainCarrier

/-- The finite alternating carrier recursion starting from an explicit seed. -/
def alternatingCarrier
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) :
    Nat → FiniteCochainCarrier
  | 0 => seed
  | i + 1 =>
      if hEven : i % 2 = 0 then
        S.rx ⟨i, hEven⟩ (alternatingCarrier seed S i)
      else
        S.rz ⟨i, by rcases even_or_odd_step i with h | h <;> simp_all⟩
          (alternatingCarrier seed S i)

@[simp]
theorem alternatingCarrier_zero
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) :
    alternatingCarrier seed S 0 = seed :=
  rfl

/-- RX has the exact typed shape `C_(2i) -> C_(2i+1)` at carrier level. -/
theorem alternatingCarrier_rx
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) (i : Nat) :
    alternatingCarrier seed S (2 * i + 1) =
      S.rx (rxStep i) (alternatingCarrier seed S (2 * i)) := by
  simp [alternatingCarrier, rxStep]

/-- RZ has the exact typed shape `C_(2i+1) -> C_(2i+2)` at carrier level. -/
theorem alternatingCarrier_rz
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) (i : Nat) :
    alternatingCarrier seed S (2 * i + 2) =
      S.rz (rzStep i) (alternatingCarrier seed S (2 * i + 1)) := by
  rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega]
  simp [alternatingCarrier, rzStep]

/-- A typed even source index inside a finite depth. -/
def finiteRxStepIndex (depth i : Nat) (h : 2 * i < depth) : StepIndex depth :=
  ⟨2 * i, h⟩

/-- A typed odd source index inside a finite depth. -/
def finiteRzStepIndex (depth i : Nat) (h : 2 * i + 1 < depth) : StepIndex depth :=
  ⟨2 * i + 1, h⟩

@[simp]
theorem finiteRx_source_val (depth i : Nat) (h : 2 * i < depth) :
    (finiteRxStepIndex depth i h).castSucc.val = 2 * i := rfl

@[simp]
theorem finiteRx_target_val (depth i : Nat) (h : 2 * i < depth) :
    (finiteRxStepIndex depth i h).succ.val = 2 * i + 1 := rfl

@[simp]
theorem finiteRz_source_val (depth i : Nat) (h : 2 * i + 1 < depth) :
    (finiteRzStepIndex depth i h).castSucc.val = 2 * i + 1 := rfl

@[simp]
theorem finiteRz_target_val (depth i : Nat) (h : 2 * i + 1 < depth) :
    (finiteRzStepIndex depth i h).succ.val = 2 * i + 2 := rfl

/-- Degree-zero coordinate type of the finite alternating family. -/
abbrev alternatingC0 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C0

/-- Degree-one coordinate type of the finite alternating family. -/
abbrev alternatingC1 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C1

/-- Degree-two coordinate type of the finite alternating family. -/
abbrev alternatingC2 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C2

instance alternatingC0Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC0 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC0

instance alternatingC1Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC1 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC1

instance alternatingC2Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC2 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC2

end BDL26FiniteAlternatingCore
end Coding
end QEC
