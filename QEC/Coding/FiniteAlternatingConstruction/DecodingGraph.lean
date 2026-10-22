import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement
import QEC.Coding.FiniteAlternatingConstruction.RZLocalReplacement
import QEC.Coding.FourDimensionalToricCode.Decoder.DirectedDistance

/-!
# Concrete alternating decoding graph

The level at index `i+1` is the Tanner one-skeleton of the presentation at
index `i`; level zero is a singleton. Inter-level edges use the intrinsic
zero-cells of the local complexes, retaining the quotient-free constructor
tags and excluding positive-dimensional connector cells.

The graph and incoming neighborhoods implement [BDL26, decoding graph and
directed distance]. They make no decoder-locality or transport assertion.
-/

namespace QEC.Coding.BDL26DecodingGraph

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

/-- The actual X/Q/Z labelling of a Tanner presentation. -/
def vertexKind (P : TannerSquarePresentation) : Vertex P → LevelVertexKind
  | .x _ => .x
  | .q _ => .q
  | .z _ => .z

/-- The undirected one-skeleton, using both given incidence matrices. -/
def tannerAdjacent (P : TannerSquarePresentation) : Vertex P → Vertex P → Prop
  | .x x, .q q => P.xq x q = true
  | .q q, .x x => P.xq x q = true
  | .q q, .z z => P.qz q z = true
  | .z z, .q q => P.qz q z = true
  | _, _ => False

instance tannerAdjacentDecidable (P : TannerSquarePresentation) (u v : Vertex P) :
    Decidable (tannerAdjacent P u v) := by
  cases u <;> cases v <;> unfold tannerAdjacent <;> infer_instance

/-- A Tanner one-skeleton whose symmetry and absence of loops are derived. -/
def tannerSkeleton (P : TannerSquarePresentation) : Locality.ConnectivityGraph (Vertex P) where
  adjacent := tannerAdjacent P
  symmetric := by intro u v h; cases u <;> cases v <;> exact h
  loopless := by intro v; cases v <;> simp [tannerAdjacent]

/-- The labelled Tanner graph has no independently supplied directed edges. -/
def tannerLevel (P : TannerSquarePresentation) : LevelGraph (Vertex P) where
  skeleton := tannerSkeleton P
  kind := vertexKind P
  skeletonDecidable := tannerAdjacentDecidable P

/-- Explicit incoming-edge formula for the orientation X to Q to Z. -/
def tannerDirected (P : TannerSquarePresentation) : Vertex P → Vertex P → Bool
  | .x x, .q q => P.xq x q
  | .q q, .z z => P.qz q z
  | _, _ => false

private theorem decide_bool_true (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

@[simp] theorem tannerLevel_edge (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.edge u v = tannerDirected P u v := by
  cases u <;> cases v <;>
    simp [tannerLevel, LevelGraph.graph, LevelGraph.directedEdge,
      tannerSkeleton, tannerAdjacent, vertexKind, tannerDirected, decide_bool_true]

theorem tannerLevel_coherence (P : TannerSquarePresentation) :
    LevelGraphSkeletonCoherence (tannerLevel P) := by
  intro u v
  cases u <;> cases v <;>
    simp [tannerLevel_edge, tannerDirected, tannerLevel, tannerSkeleton, tannerAdjacent,
      LevelGraph.graph, LevelGraph.directedEdge, vertexKind, decide_bool_true]

theorem tannerLevel_orientation (P : TannerSquarePresentation) :
    LevelGraphDirectedOrientation (tannerLevel P) :=
  (tannerLevel P).directedEdge_orientation

/-- The Tanner equivalence uses the actual presentation's vertex labels. -/
theorem tannerLevel_isomorphism (P : TannerSquarePresentation) :
    LevelGraphTannerIsomorphism (tannerLevel P) (tannerSkeleton P)
      (vertexKind P) (Equiv.refl (Vertex P)) :=
  ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

/-! ## Intrinsic local zero-cells and exact partial inverses -/

/-- Intrinsic zero-cells of the RX local complex, before degree shifts. -/
def RXZeroCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x x => DoubleCylinderVertex P x S
  | .q q => QDoubleCylinderVertex P q S
  | .z _ => BDL26FiniteTannerSquare.Two

/-- Include each local zero-cell into its actual successor coordinate tag. -/
def rxZeroInclude (P : TannerSquarePresentation) (S : OddScale) :
    (u : Vertex P) → RXZeroCell P S u → Vertex (rxReplacementPresentation P S)
  | .x x, a => .x ⟨x, a⟩
  | .q q, a => .q (Sum.inr ⟨q, a⟩)
  | .z z, a => .z (Sum.inr (z, a))

/-- Positive-dimensional RX cells are explicitly unparented. -/
def rxParent (P : TannerSquarePresentation) (S : OddScale) :
    Vertex (rxReplacementPresentation P S) → Option (Vertex P)
  | .x a => some (.x a.1)
  | .q (Sum.inl _) => none
  | .q (Sum.inr a) => some (.q a.1)
  | .z (Sum.inl _) => none
  | .z (Sum.inr a) => some (.z a.1)

/-- RX parent incidence is exactly membership in the included intrinsic zero-cells. -/
theorem rxParent_iff (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) (v : Vertex (rxReplacementPresentation P S)) :
    rxParent P S v = some u ↔ ∃ a : RXZeroCell P S u, rxZeroInclude P S u a = v := by
  constructor
  · intro h
    cases v with
    | x a =>
        have hu : Vertex.x a.1 = u := Option.some.inj h
        subst u
        exact ⟨a.2, rfl⟩
    | q a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.q a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | z a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.z a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
  · rintro ⟨a, rfl⟩
    cases u <;> rfl

/-- Intrinsic zero-cells of the RZ local complex, before cochain transposition. -/
def RZZeroCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x _ => BDL26FiniteTannerSquare.Two
  | .q q => QDoubleCylinderVertex (transposePresentation P) q S
  | .z z => ZDoubleCylinderVertex P z S

/-- Include the zero-cells in the materialized RZ successor. -/
def rzZeroInclude (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) : (u : Vertex P) → RZZeroCell P S u →
      Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
  | .x x, a => .x (Sum.inr (x, a))
  | .q q, a => .q (Sum.inr ⟨q, a⟩)
  | .z z, a => .z ⟨z, a⟩

/-- Positive-dimensional RZ cells are explicitly unparented. -/
def rzParent (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → Option (Vertex P)
  | .x (Sum.inl _) => none
  | .x (Sum.inr a) => some (.x a.1)
  | .q (Sum.inl _) => none
  | .q (Sum.inr a) => some (.q a.1)
  | .z a => some (.z a.1)

/-- RZ incidence uses the same intrinsic-zero-cell criterion as RX. -/
theorem rzParent_iff (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (u : Vertex P)
    (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    rzParent P A S v = some u ↔
      ∃ a : RZZeroCell P S u, rzZeroInclude P A S u a = v := by
  constructor
  · intro h
    cases v with
    | x a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.x a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | q a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.q a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | z a =>
        have hu : Vertex.z a.1 = u := Option.some.inj h
        subst u
        exact ⟨a.2, rfl⟩
  · rintro ⟨a, rfl⟩
    cases u <;> rfl

/-! ## Recursive construction from the audited seed -/

/-- The constructor state retains the proved admissibility needed for the next step. -/
structure ConstructionState where
  presentation : TannerSquarePresentation
  admissible : TannerSquareAdmissibleV4 presentation
  regular : TannerSquareCellularRegular presentation
  selectedX : presentation.X

/-- The finite seed, including its existing proved regularity. -/
def baseState : ConstructionState where
  presentation := baseTannerSquarePresentation
  admissible := baseTannerSquareAdmissibleV4
  regular := baseTannerSquareCellularRegular
  selectedX := (0 : BaseX)

/-- Actual RX replacement; all validity fields come from the replacement proofs. -/
noncomputable def rxState (S : OddScale) (C : ConstructionState) : ConstructionState where
  presentation := rxReplacementPresentation C.presentation S
  admissible := rxReplacementAdmissibleV4 C.presentation C.admissible C.regular S
  regular := rxReplacementCellularRegular C.presentation C.regular S
  selectedX := rxOriginalCentralXCoordinate C.presentation S C.selectedX 0

/-- Actual RZ replacement, retaining the source-selected coordinate order. -/
noncomputable def rzState (S : OddScale) (C : ConstructionState) : ConstructionState where
  presentation := BDL26RZLocalReplacement.rzReplacementPresentation
    C.presentation C.admissible.toTannerSquareAdmissible S
  admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4
    C.presentation C.admissible C.regular S
  regular := BDL26RZLocalReplacement.rzReplacementCellularRegular
    C.presentation C.admissible.toTannerSquareAdmissibleV3 C.regular S
  selectedX := Sum.inr (C.selectedX, 0)

/-- Even source levels use RX and odd source levels use RZ. -/
noncomputable def nextState (S : OddScale) (n : Nat) (C : ConstructionState) :
    ConstructionState := if n % 2 = 0 then rxState S C else rzState S C

/-- Recursive actual Tanner presentations, with no caller-supplied successor. -/
noncomputable def state (S : OddScale) : Nat → ConstructionState
  | 0 => baseState
  | n + 1 => nextState S n (state S n)

/-- Reindex a successor vertex along the selected even-step presentation equality. -/
noncomputable def nextRXVertex (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) (v : Vertex (nextState S n C).presentation) :
    Vertex (rxReplacementPresentation C.presentation S) :=
  cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
    (show nextState S n C = rxState S C from if_pos h)) v

/-- Reindex a successor vertex along the selected odd-step presentation equality. -/
noncomputable def nextRZVertex (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬n % 2 = 0) (v : Vertex (nextState S n C).presentation) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation
      C.presentation C.admissible.toTannerSquareAdmissible S) :=
  cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
    (show nextState S n C = rzState S C from if_neg h)) v

/-- A local region before finset enumeration, from the intrinsic zero-cell inclusions. -/
noncomputable def nextRegionMember (S : OddScale) (n : Nat) (C : ConstructionState) :
    Vertex C.presentation → Vertex (nextState S n C).presentation → Prop :=
  if h : n % 2 = 0 then
    fun u v => ∃ a, rxZeroInclude C.presentation S u a = nextRXVertex S n C h v
  else
    fun u v => ∃ a, rzZeroInclude C.presentation C.admissible.toTannerSquareAdmissible S u a =
      nextRZVertex S n C h v

/-- The adjacent parent is computed by the selected replacement constructor. -/
noncomputable def nextParent (S : OddScale) (n : Nat) (C : ConstructionState) :
    Vertex (nextState S n C).presentation → Option (Vertex C.presentation) :=
  if h : n % 2 = 0 then
    fun v => rxParent C.presentation S (nextRXVertex S n C h v)
  else
    fun v => rzParent C.presentation C.admissible.toTannerSquareAdmissible S
      (nextRZVertex S n C h v)

theorem nextParent_iff (S : OddScale) (n : Nat) (C : ConstructionState)
    (u : Vertex C.presentation) (v : Vertex (nextState S n C).presentation) :
    nextParent S n C v = some u ↔ nextRegionMember S n C u v := by
  by_cases h : n % 2 = 0
  · simp only [nextParent, nextRegionMember, dif_pos h]
    exact rxParent_iff C.presentation S u (nextRXVertex S n C h v)
  · simp only [nextParent, nextRegionMember, dif_neg h]
    exact rzParent_iff C.presentation C.admissible.toTannerSquareAdmissible S u
      (nextRZVertex S n C h v)

/-- Decoding level zero is a singleton, and level i+1 uses Tanner presentation i. -/
def GraphVertex (S : OddScale) : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex (state S n).presentation

noncomputable instance graphVertexFintype (S : OddScale) (n : Nat) :
    Fintype (GraphVertex S n) := by cases n <;> dsimp [GraphVertex] <;> infer_instance

noncomputable instance graphVertexDecidableEq (S : OddScale) (n : Nat) :
    DecidableEq (GraphVertex S n) := by
  cases n <;> dsimp [GraphVertex] <;> infer_instance

/-- The singleton root has no intra-level edges. -/
def rootLevel : LevelGraph Unit where
  skeleton := ⟨fun _ _ => False, fun _ _ h => h, fun _ h => h⟩
  kind := fun _ => .x
  skeletonDecidable := fun _ _ => inferInstance

/-- Each positive level is the exact labelled predecessor Tanner one-skeleton. -/
noncomputable def level (S : OddScale) : (n : Nat) → LevelGraph (GraphVertex S n)
  | 0 => rootLevel
  | n + 1 => tannerLevel (state S n).presentation

/-- The root exception and the adjacent-only local-region incidence. -/
noncomputable def regionMember (S : OddScale) :
    (n : Nat) → GraphVertex S n → GraphVertex S (n + 1) → Prop
  | 0, _, _ => True
  | n + 1, u, v => nextRegionMember S n (state S n) u v

/-- Enumerate actual intrinsic zero-cell membership at one adjacent pair of levels. -/
noncomputable def localRegion (S : OddScale) (n : Nat) (u : GraphVertex S n) :
    Finset (GraphVertex S (n + 1)) := by
  classical
  exact Finset.univ.filter (regionMember S n u)

/-- Adjacent partial parent, with the separately stipulated root exception. -/
noncomputable def parent (S : OddScale) :
    (n : Nat) → GraphVertex S (n + 1) → Option (GraphVertex S n)
  | 0, _ => some ()
  | n + 1, v => nextParent S n (state S n) v

/-- The concrete zero-cell incidence theorem for every adjacent pair of levels. -/
theorem parent_mem_iff (S : OddScale) (n : Nat)
    (u : GraphVertex S n) (v : GraphVertex S (n + 1)) :
    parent S n v = some u ↔ v ∈ localRegion S n u := by
  classical
  simp only [localRegion, Finset.mem_filter, Finset.mem_univ, true_and]
  cases n with
  | zero => cases u; simp [parent, regionMember]
  | succ n => exact nextParent_iff S n (state S n) u v

/-- Local zero-cell regions are disjoint because their concrete tags determine the parent. -/
theorem localRegion_disjoint (S : OddScale) (n : Nat)
    (u w : GraphVertex S n) (hne : u ≠ w) :
    Disjoint (localRegion S n u) (localRegion S n w) := by
  apply Finset.disjoint_left.mpr
  intro v hu hw
  have hu' := (parent_mem_iff S n u v).mpr hu
  have hw' := (parent_mem_iff S n w v).mpr hw
  exact hne (Option.some.inj (hu'.symm.trans hw'))

/-- Finite truncation of the concrete infinite recursion, at any requested depth. -/
noncomputable def decodingGraph (S : OddScale) (depth : Nat) :
    DecodingGraphFamily depth (fun i => GraphVertex S i.val) where
  level := fun i => level S i.val
  interLevel := fun i u v => by
    classical
    exact decide (v ∈ localRegion S i.val u)
  root := ()
  root_unique := by intro v; cases v; rfl

/-- The raw graph's inter-level edge is exactly adjacent intrinsic-zero-cell membership. -/
theorem interLevel_mem_iff (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (u : GraphVertex S i.val) (v : GraphVertex S (i.val + 1)) :
    (decodingGraph S depth).interLevel i u v = true ↔ v ∈ localRegion S i.val u := by
  classical
  simp [decodingGraph]

/-- The parent field required by the raw geometry contract, proved from local inclusion. -/
theorem parent_interLevel_iff (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (u : GraphVertex S i.val) (v : GraphVertex S (i.val + 1)) :
    parent S i.val v = some u ↔ (decodingGraph S depth).interLevel i u v = true :=
  (parent_mem_iff S i.val u v).trans (interLevel_mem_iff S depth i u v).symm

theorem root_connected (S : OddScale) (depth : Nat) (hdepth : 0 < depth) :
    (decodingGraph S depth).RootConnectedToLevelOne hdepth := by
  intro v
  classical
  simp [decodingGraph, localRegion, regionMember]

/-- Level two is Tanner presentation one, the actual RX successor of the seed. -/
theorem level_two (S : OddScale) :
    level S 2 = tannerLevel (rxState S baseState).presentation := by
  rfl

/-! ## Exact incoming radius-one and radius-two carriers -/

/-- Expanding one directed step retains the centre and its incoming neighbors. -/
theorem reachable_one (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.reachableWithin 1 u v = true ↔
      u = v ∨ tannerDirected P u v = true := by
  simp [DirectedGraph.reachableWithin, tannerLevel_edge]

/-- Two directed steps retain the centre, incoming neighbors, and two-edge predecessors. -/
theorem reachable_two (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.reachableWithin 2 u v = true ↔
      u = v ∨ tannerDirected P u v = true ∨
        ∃ w : Vertex P, tannerDirected P u w = true ∧ tannerDirected P w v = true := by
  simp only [DirectedGraph.reachableWithin, Bool.or_eq_true,
    decide_eq_true_eq, tannerLevel_edge]
  aesop

/-- Every constructed presentation has at least two distinct X vertices. -/
theorem state_pair (S : OddScale) (n : Nat) :
    Nonempty (Fin 2 ↪ Vertex (state S n).presentation) := by
  cases n with
  | zero =>
      refine ⟨⟨fun i => .x i, ?_⟩⟩
      intro i j h
      exact Vertex.x.inj h
  | succ n =>
      unfold state nextState
      split
      · let P := (state S n).presentation
        let x := (state S n).selectedX
        refine ⟨⟨fun i => .x (rxOriginalCentralXCoordinate P S x i), ?_⟩⟩
        intro i j h
        exact congrArg (fun c : (rxReplacementPresentation P S).X => c.2.1)
          (Vertex.x.inj h)
      · let C := state S n
        refine ⟨⟨fun i => .x (Sum.inr (C.selectedX, i)), ?_⟩⟩
        intro i j h
        exact congrArg Prod.snd (Sum.inr.inj (Vertex.x.inj h))

theorem state_card_ge_two (S : OddScale) (n : Nat) :
    2 ≤ Fintype.card (Vertex (state S n).presentation) := by
  obtain ⟨e⟩ := state_pair S n
  simpa using Fintype.card_le_of_injective e e.injective

/-- The graph radius-one carrier used by the raw correction-region interface. -/
theorem mem_radius_one (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ LocalRegion.directedNeighborhood (tannerLevel (state S n).presentation).graph v 1 ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true := by
  simp only [LocalRegion.directedNeighborhood, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [DirectedGraph.distance_le_iff_reachableWithin _ u v 1 (by
    have h := state_card_ge_two S n
    omega)]
  exact reachable_one _ u v

/-- The exact raw coarse-syndrome radius-two carrier, with directed incoming paths. -/
theorem mem_radius_two (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ LocalRegion.directedNeighborhood (tannerLevel (state S n).presentation).graph v 2 ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true ∨
        ∃ w : Vertex (state S n).presentation,
          tannerDirected (state S n).presentation u w = true ∧
          tannerDirected (state S n).presentation w v = true := by
  simp only [LocalRegion.directedNeighborhood, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [DirectedGraph.distance_le_iff_reachableWithin _ u v 2 (state_card_ge_two S n)]
  exact reachable_two _ u v

/-- A two-edge directed predecessor of Z must be X through an actual Q neighbor. -/
theorem tanner_two_edge_xz (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    (∃ w : Vertex P,
      tannerDirected P (.x x) w = true ∧ tannerDirected P w (.z z) = true) ↔
      ∃ q : P.Q, P.xq x q = true ∧ P.qz q z = true := by
  constructor
  · rintro ⟨w, hw⟩
    cases w with
    | x _ => simp [tannerDirected] at hw
    | q q => exact ⟨q, hw⟩
    | z _ => simp [tannerDirected] at hw
  · rintro ⟨q, hq⟩
    exact ⟨.q q, hq⟩

/-- The source X-to-Z radius-two formula has precisely the common-Q incidence witness. -/
theorem x_mem_z_radius_two (S : OddScale) (n : Nat)
    (x : (state S n).presentation.X) (z : (state S n).presentation.Z) :
    Vertex.x x ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S n).presentation).graph (.z z) 2 ↔
      ∃ q : (state S n).presentation.Q,
        (state S n).presentation.xq x q = true ∧
        (state S n).presentation.qz q z = true := by
  rw [mem_radius_two]
  simpa only [reduceCtorEq, tannerDirected, Bool.false_eq_true, false_or] using
    tanner_two_edge_xz (state S n).presentation x z

/-- Concrete correction region in the existing raw local-region API. -/
noncomputable def correctionRegion (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : LocalRegion (Vertex (state S n).presentation) :=
  LocalRegion.correctionRegion (tannerLevel (state S n).presentation).graph v

/-- Concrete coarse-syndrome region in the existing raw local-region API. -/
noncomputable def syndromeRegion (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : LocalRegion (Vertex (state S n).presentation) :=
  LocalRegion.syndromeRegion (tannerLevel (state S n).presentation).graph v

@[simp] theorem correctionRegion_mem (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (correctionRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true :=
  mem_radius_one S n u v

@[simp] theorem syndromeRegion_mem (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (syndromeRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true ∨
        ∃ w : Vertex (state S n).presentation,
          tannerDirected (state S n).presentation u w = true ∧
          tannerDirected (state S n).presentation w v = true :=
  mem_radius_two S n u v

/-- The root's self-distance is zero despite the absence of edges. -/
theorem root_distance : rootLevel.graph.distance () () = (0 : WithTop Nat) := by
  decide

/-- Every incoming root neighborhood contains exactly the singleton root. -/
theorem root_neighborhood (radius : Nat) :
    LocalRegion.directedNeighborhood rootLevel.graph () radius = {()} := by
  ext u
  cases u
  simp [LocalRegion.directedNeighborhood, root_distance]

/-! ## Assembly boundary for the versioned raw geometry contract -/

/-- Install the concrete graph-parent portion of the raw contract. Coordinate
ownership and local-support equalities are separate inputs: this adapter does
not prove that arbitrary coordinate owners represent the constructed complexes.
No parent map, inter-level equality, or root-incidence proof is supplied by the caller. -/
noncomputable def assembleOwnerIncidence (S : OddScale) (depth : Nat)
    (Syn Cor : LevelIndex depth → Type)
    [∀ i, Fintype (Syn i)] [∀ i, DecidableEq (Syn i)]
    [∀ i, Fintype (Cor i)] [∀ i, DecidableEq (Cor i)]
    (synOwner : ∀ i, Syn i → Option (GraphVertex S i.val))
    (corOwner : ∀ i, Cor i → Option (GraphVertex S i.val))
    (regions : ∀ i, LocalComplexData (GraphVertex S i.val) (Syn i) (Cor i))
    (synIff : ∀ i u c, synOwner i c = some u ↔ c ∈ (regions i).syndromeRegion u)
    (corIff : ∀ i u c, corOwner i c = some u ↔ c ∈ (regions i).correctionRegion u) :
    AdjacentLevelOwnerIncidence depth (fun i => GraphVertex S i.val)
      Syn Cor (decodingGraph S depth) where
  syndromeOwner := synOwner
  correctionOwner := corOwner
  syndromeRegion := fun i => (regions i).syndromeRegion
  correctionRegion := fun i => (regions i).correctionRegion
  syndromeOwner_mem_iff := synIff
  correctionOwner_mem_iff := corIff
  syndromeOwner_none_iff := by
    intro i c
    constructor
    · intro h u hm
      have heq := (synIff i u c).mpr hm
      rw [h] at heq
      cases heq
    · intro h
      cases heq : synOwner i c with
      | none => rfl
      | some u => exact (h u ((synIff i u c).mp heq)).elim
  correctionOwner_none_iff := by
    intro i c
    constructor
    · intro h u hm
      have heq := (corIff i u c).mpr hm
      rw [h] at heq
      cases heq
    · intro h
      cases heq : corOwner i c with
      | none => rfl
      | some u => exact (h u ((corIff i u c).mp heq)).elim
  parentIncidence := fun i => parent S i.val
  parentIncidence_mem_iff := fun i u v => parent_interLevel_iff S depth i u v
  root_parent_incidence := fun _ _ => rfl

end QEC.Coding.BDL26DecodingGraph
