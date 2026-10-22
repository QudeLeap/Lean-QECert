import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder
import QEC.Coding.FiniteAlternatingConstruction.RZSupportedBoundary

/-!
# Actual indexed RZ decoder steps

The adapter uses the actual Z-edge correction fibres and Z-vertex syndrome
blocks. Its F07 and F09 obligations are proved externally from supported
boundary exactness and actual incidence parity. These are individual steps;
no recursion below physical C₂ or complete history is asserted here.
-/

namespace QEC.Coding.BDL26RZDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators

universe u


noncomputable local instance rzQDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _
noncomputable local instance rzZDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZZ P S) := Classical.decEq _

/-- Only local Z-edge coordinates belong to this step's correction regions.
The Q-block coordinates remain available to the induced parity projection. -/
def blockCorrectionOwner (P : TannerSquarePresentation) (S : OddScale) :
    RZQ P S → Option (Vertex P)
  | .inl ⟨z, _⟩ => some (.z z)
  | .inr _ => none

theorem blockCorrectionOwner_region (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      Finset.univ.filter (fun q => blockCorrectionOwner P S q = some (.z z)) := by
  ext q
  simp only [BDL26RZSupportedBoundary.correctionRegion, fiberRegion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rcases q with ⟨w,e⟩ | ⟨q,v⟩
  · change (Vertex.z w = Vertex.z z) ↔ (some (Vertex.z w) = some (Vertex.z z))
    simp only [Option.some.injEq]
  · change (Vertex.q q = Vertex.z z) ↔ (none = some (Vertex.z z))
    simp

private theorem rootLift_outside (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) (p : RZZ P S) (hp : p ∉ blockRegion P S z) :
    rootLift P A S z b p = 0 := by
  by_contra hn
  exact hp (rootLift_support P A S z b (by simpa [hammingSupport] using hn))

private theorem rootLift_region_parity (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) (b : BDL26Field) :
    (∑ p ∈ blockRegion P S z, rootLift P A S z b p) = b := by
  rw [← blockParity_eq_region_sum, rootLift, blockParity_map2]
  simp

private theorem block_radius (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (p : RZZ P S) (hp : p ∈ blockRegion P S z) :
    DirectedGraph.distance (tannerLevel P).graph (.z p.1) (.z z) = 0 := by
  have hz : p.1 = z := (Finset.mem_filter.mp hp).2
  rw [hz]
  let G := (tannerLevel P).graph
  let v : Vertex P := .z z
  have hreach : ∀ n, DirectedGraph.reachableWithin G n v v = true := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.reachableWithin]
    | succ n ih => simp [DirectedGraph.reachableWithin, ih]
  have haux : ∀ n, DirectedGraph.distanceAux G v v n = some 0 := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.distanceAux, hreach]
    | succ n ih => simp [DirectedGraph.distanceAux, ih, hreach]
  change DirectedGraph.distance G v v = 0
  simp [DirectedGraph.distance, haux]

/-- Private proof package, constructed below from actual replacement geometry. -/
private structure EndpointData (P U : TannerSquarePresentation) where
  topCenter : U.Z → Vertex P
  owner : U.Q → Option (Vertex P)
  region : P.Z → Finset U.Z
  corrections : P.Z → Finset U.Q
  lift : P.Z → BDL26Field → Word BDL26Field U.Z
  map2 : Word BDL26Field P.Z →ₗ[BDL26Field] Word BDL26Field U.Z
  projection : Word BDL26Field U.Q →ₗ[BDL26Field] Word BDL26Field P.Q
  cover : ∀ p, ∃ z, p ∈ region z
  disjoint : ∀ z w, z ≠ w → Disjoint (region z) (region w)
  corrections_disjoint : ∀ z w, z ≠ w → Disjoint (corrections z) (corrections w)
  coherence : ∀ z, corrections z = Finset.univ.filter (fun q => owner q = some (.z z))
  lift_supported : ∀ z b p, p ∉ region z → lift z b p = 0
  lift_parity : ∀ z b, (∑ p ∈ region z, lift z b p) = b
  decomposition : ∀ sigma, map2 sigma = ∑ z, lift z (sigma z)
  boundary_supported : ∀ z (f : Word BDL26Field U.Q),
    (∀ q, q ∉ corrections z → f q = 0) →
      ∀ p, p ∉ region z → tannerCoboundary1 U f p = 0
  radius : ∀ z p, p ∈ region z →
    DirectedGraph.distance (tannerLevel P).graph (topCenter p) (.z z) = 0

private theorem blockRegion_cover (P : TannerSquarePresentation) (S : OddScale) :
    ∀ p : RZZ P S, ∃ z : P.Z, p ∈ blockRegion P S z := by
  intro p
  exact ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

private theorem corrections_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    ∀ z w : P.Z, z ≠ w → Disjoint
      (BDL26RZSupportedBoundary.correctionRegion P S z)
      (BDL26RZSupportedBoundary.correctionRegion P S w) := by
  intro z w h
  apply Finset.disjoint_left.mpr
  intro q hz hw
  exact h (Vertex.z.inj ((Finset.mem_filter.mp hz).2.symm.trans
    (Finset.mem_filter.mp hw).2))

private theorem ownerRegionForFintype (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (F : Fintype (RZQ P S))
    (D : DecidablePred (fun q : RZQ P S => blockCorrectionOwner P S q = some (Vertex.z z))) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      @Finset.filter (RZQ P S) (fun q => blockCorrectionOwner P S q = some (Vertex.z z))
        D (@Finset.univ (RZQ P S) F) := by
  ext q
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.ext_iff.mp (blockCorrectionOwner_region P S z) q)

private theorem actualCoherence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      (Finset.univ : Finset ((rzReplacementPresentation P A.toTannerSquareAdmissible S).Q)).filter
        (fun q => blockCorrectionOwner P S q = some (Vertex.z z)) :=
  ownerRegionForFintype P S z _ _

private noncomputable def actualEndpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointData P (rzReplacementPresentation P A.toTannerSquareAdmissible S) where
  topCenter := fun p => .z p.1
  owner := blockCorrectionOwner P S
  region := blockRegion P S
  corrections := BDL26RZSupportedBoundary.correctionRegion P S
  lift := rootLift P A S
  map2 := map2Coord P A S
  projection := rzQParity P S
  cover := blockRegion_cover P S
  disjoint := fun _ _ h => blockRegion_disjoint P S h
  corrections_disjoint := corrections_disjoint P S
  coherence := actualCoherence P A S
  lift_supported := rootLift_outside P A S
  lift_parity := rootLift_region_parity P A S
  decomposition := fun sigma => (sum_rootLift P A S sigma).symm
  boundary_supported := fun z f hf =>
    BDL26RZSupportedBoundary.coboundary_supported P A S z ⟨f,hf⟩
  radius := block_radius P S

private def transportEndpoint (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V) : EndpointData P U := h.symm ▸ G

private theorem transportEndpoint_property (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V)
    (property : (T : TannerSquarePresentation) → EndpointData P T → Prop)
    (hg : property V G) : property U (transportEndpoint P U V h G) := by
  cases h
  exact hg

private theorem transportEndpoint_fields (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V) :
    HEq (transportEndpoint P U V h G).region G.region ∧
    HEq (transportEndpoint P U V h G).corrections G.corrections ∧
    HEq (transportEndpoint P U V h G).owner G.owner ∧
    HEq (transportEndpoint P U V h G).projection G.projection ∧
    HEq (transportEndpoint P U V h G).map2 G.map2 := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private noncomputable def endpointBoundary {P U : TannerSquarePresentation}
    (G : EndpointData P U) (z : P.Z) :
    supportedSubmodule (G.corrections z) →ₗ[BDL26Field] supportedSubmodule (G.region z) where
  toFun f := ⟨tannerCoboundary1 U f.1, G.boundary_supported z f.1 f.2⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp

private def EndpointF07 {P U : TannerSquarePresentation} (G : EndpointData P U) : Prop :=
  ∀ z, ∃ e : ((supportedSubmodule (G.region z)) ⧸ LinearMap.range (endpointBoundary G z))
    ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (endpointBoundary G z)).mkQ r) = ∑ p ∈ G.region z, r.1 p

private theorem actualEndpoint_F07 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointF07 (actualEndpoint P A S) := by
  intro z
  exact ⟨BDL26RZSupportedBoundary.quotientEquiv P A S z,
    BDL26RZSupportedBoundary.quotientEquiv_mkQ P A S z⟩

private def EndpointF09 {P U : TannerSquarePresentation} (G : EndpointData P U) : Prop :=
  ∀ e, (fun z => ∑ p ∈ G.region z, tannerCoboundary1 U e p) =
    tannerCoboundary1 P (G.projection e)

private theorem actualEndpoint_F09 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointF09 (actualEndpoint P A S) := by
  intro e
  funext z
  exact (blockParity_eq_region_sum P S (rzCoboundary1 P A S e) z).symm.trans
    (rzCoboundary1_blockParity P A S e z)

private def EndpointResidualZero {P U : TannerSquarePresentation}
    (G : EndpointData P U) : Prop :=
  ∀ sigma z, maskWord (G.region z) (G.map2 sigma) +
    G.lift z (∑ p ∈ G.region z, G.map2 sigma p) = 0

private theorem mask_blockRegion (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : Word BDL26Field (RZZ P S)) :
    maskWord (blockRegion P S z) e = blockPart P S z e := by
  funext p
  change (if p ∈ blockRegion P S z then e p else 0) = _
  simp only [blockRegion, fiberRegion, Finset.mem_filter, Finset.mem_univ, true_and,
    blockPart, fiberPart]
  rfl

private theorem actualEndpoint_residual (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointResidualZero (actualEndpoint P A S) := by
  intro sigma z
  change maskWord (blockRegion P S z) ((map2Coord P A S) sigma) +
    rootLift P A S z (∑ p ∈ blockRegion P S z, (map2Coord P A S) sigma p) = 0
  rw [mask_blockRegion, ← blockParity_eq_region_sum]
  exact localResidual_map2_eq_zero P A S sigma z

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

private theorem stateSuccRZ (h : ¬i.val % 2 = 0) :
    state S (i.val + 1) = rzState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_neg h

private noncomputable def endpointAt (h : ¬i.val % 2 = 0) :
    EndpointData (state S i.val).presentation (state S (i.val + 1)).presentation :=
  transportEndpoint _ _ _ (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)

private theorem endpointAt_map2 (h : ¬i.val % 2 = 0) :
    (endpointAt S depth i h).map2 = (indexedEdgeMap S depth i).map2 := by
  have hfields := transportEndpoint_fields _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
  have hm := (indexedDecoderData_selected_rz S depth i h).2.2
  rw [selectedMap_eq] at hm
  exact eq_of_heq (hfields.2.2.2.2.trans hm.symm)

/-- Actual indexed RZ data; its entire endpoint geometry is transported once. -/
noncomputable def rzData (h : ¬i.val % 2 = 0) :
    RZCoarseGrainingData (indexedDecoderData S depth) i
      (Vertex (state S i.val).presentation) := by
  let G := endpointAt S depth i h
  refine
    { levelGraph := tannerLevel (state S i.val).presentation
      center := Vertex.z
      topCenter := G.topCenter
      correctionOwner := G.owner
      coarseRegion := G.region
      correctionInputRegion := G.region
      correctionRegion := G.corrections
      lift := G.lift
      induced := ⟨G.projection⟩
      coarseRegion_cover := G.cover
      coarseRegion_disjoint := G.disjoint
      correctionInputRegion_subset := fun _ => Finset.Subset.refl _
      correctionRegion_disjoint := G.corrections_disjoint
      correctionRegion_coherence := G.coherence
      lift_supported := G.lift_supported
      lift_parity := G.lift_parity
      induced_syndrome_decomposition := ?_
      local_boundary_supported := ?_
      topRegion_radius_two := ?_
      correctionInput_radius_one := ?_ }
  · intro sigma
    change (indexedEdgeMap S depth i).map2 sigma = _
    rw [← endpointAt_map2 S depth i h]
    exact G.decomposition sigma
  · intro z f hf p hp
    change ((indexedFamily S depth).coboundary1 i.succ) f p = 0
    rw [indexedFamily_coboundary1]
    exact G.boundary_supported z f hf p hp
  · intro z p hp
    rw [G.radius z p hp]
    simp
  · intro z p hp
    rw [G.radius z p hp]
    simp

/-- The indexed regions and projection are the actual constructor objects,
with only the defining upper-carrier transport. -/
theorem rzData_coordinates (h : ¬i.val % 2 = 0) :
    HEq (rzData S depth i h).coarseRegion
      (blockRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionRegion
      (BDL26RZSupportedBoundary.correctionRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionOwner
      (blockCorrectionOwner (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).induced.correctionProjection
      (rzQParity (state S i.val).presentation S) := by
  have hf := transportEndpoint_fields _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

/-- Every indexed syndrome coordinate has its actual Z-block owner. -/
theorem rzData_topCenter_is_z (h : ¬i.val % 2 = 0)
    (p : FamilyZ S depth i.succ) :
    ∃ z, (rzData S depth i h).topCenter p = Vertex.z z := by
  have hg := transportEndpoint_property _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
    (fun U G => ∀ q : U.Z, ∃ z, G.topCenter q = Vertex.z z)
    (by intro q; exact ⟨q.1, rfl⟩)
  exact hg p

/-- A nonzero selected image retains a nonzero input at its actual block owner.
This follows from the actual root lift before transporting the upper carrier. -/
theorem rzData_map2_active_owner (h : ¬i.val % 2 = 0)
    (s : Word BDL26Field (FamilyZ S depth i.castSucc))
    (p : FamilyZ S depth i.succ)
    (hp : ((indexedDecoderData S depth).selectedMap i).map2 s p ≠ 0) :
    ∃ z, (rzData S depth i h).topCenter p = Vertex.z z ∧ s z ≠ 0 := by
  have hg := transportEndpoint_property _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
    (fun U G => ∀ (t : Word BDL26Field (state S i.val).presentation.Z)
      (q : U.Z), G.map2 t q ≠ 0 → ∃ z, G.topCenter q = Vertex.z z ∧ t z ≠ 0)
    (by
      intro t q hq
      refine ⟨q.1, rfl, ?_⟩
      intro hz
      apply hq
      change map2Coord _ _ S t q = 0
      rcases q with ⟨z,v⟩
      rw [BDL26OwnerParentObstruction.rzMap2_apply]
      simp only [hz, ite_self])
  apply hg s p
  change (endpointAt S depth i h).map2 s p ≠ 0
  rw [endpointAt_map2, ← selectedMap_eq]
  exact hp

/-- F07 is an external theorem from actual supported-boundary exactness. -/
theorem rzData_localTopCohomology (h : ¬i.val % 2 = 0) :
    LocalTopCohomologyIdentification (rzData S depth i h) := by
  have hg : EndpointF07 (endpointAt S depth i h) :=
    transportEndpoint_property _ _ _
      (congrArg ConstructionState.presentation (stateSuccRZ S depth i h)) _
      (fun _ G => EndpointF07 G)
      (actualEndpoint_F07 (state S i.val).presentation (state S i.val).admissible S)
  have hb (z : (state S i.val).presentation.Z) :
      localBoundaryMap (rzData S depth i h) z = endpointBoundary (endpointAt S depth i h) z := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change ((indexedFamily S depth).coboundary1 i.succ) f.1 =
      tannerCoboundary1 (state S (i.val + 1)).presentation f.1
    rw [indexedFamily_coboundary1]
    rfl
  intro z
  change ∃ e : ((supportedSubmodule ((endpointAt S depth i h).region z)) ⧸
      LinearMap.range (localBoundaryMap (rzData S depth i h) z)) ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (localBoundaryMap (rzData S depth i h) z)).mkQ r) =
      ∑ p ∈ (endpointAt S depth i h).region z, r.1 p
  rw [hb z]
  exact hg z

/-- F09 follows from the actual materialized RZ incidence calculation. -/
theorem rzData_inducedCoboundaryCompatibility (h : ¬i.val % 2 = 0) :
    InducedCoboundaryCompatibility (rzData S depth i h) := by
  have hg : EndpointF09 (endpointAt S depth i h) :=
    transportEndpoint_property _ _ _
      (congrArg ConstructionState.presentation (stateSuccRZ S depth i h)) _
      (fun _ G => EndpointF09 G)
      (actualEndpoint_F09 (state S i.val).presentation (state S i.val).admissible S)
  intro e
  change (fun z => ∑ p ∈ (endpointAt S depth i h).region z,
    ((indexedFamily S depth).coboundary1 i.succ) e p) =
    ((indexedFamily S depth).coboundary1 i.castSucc) ((endpointAt S depth i h).projection e)
  rw [indexedFamily_coboundary1, indexedFamily_coboundary1]
  exact hg e

private theorem upper_even (h : ¬i.val % 2 = 0) : i.succ.val % 2 = 0 := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 2)
  change (i.val + 1) % 2 = 0
  omega

/-- Canonical output with both concrete contract slices discharged. -/
noncomputable def rzStepOutput (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  AuditedLeafAdapters.rzOutput (rzData S depth i h)
    (rzData_localTopCohomology S depth i h)
    (rzData_inducedCoboundaryCompatibility S depth i h)
    (upper_even depth i h) sigma

theorem rzStepOutput_coarse_apply (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (z : (state S i.val).presentation.Z) :
    (rzStepOutput S depth i h sigma).coarse.val z =
      ∑ p ∈ (rzData S depth i h).coarseRegion z, sigma.val p :=
  AuditedLeafAdapters.rzOutput_coarse_apply _ _ _ _ _ _

theorem rzStepOutput_relation (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigma.val = (indexedFamily S depth).coboundary1 i.succ
      (rzStepOutput S depth i h sigma).correction +
      ((indexedDecoderData S depth).selectedMap i).map2
        (rzStepOutput S depth i h sigma).coarse.val :=
  (rzStepOutput S depth i h sigma).relation

theorem rzStepOutput_weight (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    HammingWeight (rzStepOutput S depth i h sigma).coarse.val ≤ HammingWeight sigma.val :=
  AuditedLeafAdapters.rzOutput_weight _ _ _ _ _

/-- Expose the exact list at the concrete wrapper, before dependent get indices. -/
theorem rzStepOutput_localComponents (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rzStepOutput S depth i h sigma).localComponents =
      (Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
        (fun z => localCorrectionComponent (rzData S depth i h)
          (rzData_localTopCohomology S depth i h) z sigma.val) := rfl

/-- The owner is read from the very enumeration used to construct the output. -/
noncomputable def componentOwner (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    (state S i.val).presentation.Z :=
  (Finset.univ : Finset ((state S i.val).presentation.Z)).toList.get
    ⟨j.val, by
      simpa (config := { instances := true }) only [rzStepOutput_localComponents,
        List.length_map] using j.isLt⟩

theorem rzStepOutput_component_eq (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    (rzStepOutput S depth i h sigma).componentAt j =
      localCorrectionComponent (rzData S depth i h)
        (rzData_localTopCohomology S depth i h)
        (componentOwner S depth i h sigma j) sigma.val := by
  change ((Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
    (fun z => localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z sigma.val)).get j = _
  change ((Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
    (fun z => localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z sigma.val))[j.val] = _
  rw [List.getElem_map]
  rfl

/-- Every actual lower Z owner occurs in the ordered output exactly once. -/
theorem componentOwner_bijective (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    Function.Bijective (componentOwner S depth i h sigma) := by
  let zs := (Finset.univ : Finset ((state S i.val).presentation.Z)).toList
  have hlen : (rzStepOutput S depth i h sigma).localComponents.length = zs.length := by
    simp only [rzStepOutput_localComponents, List.length_map]
    rfl
  constructor
  · intro j k he
    apply Fin.ext
    have hn : zs.Nodup := Finset.nodup_toList _
    have hv := hn.get_inj_iff.mp he
    exact congrArg (fun t : Fin zs.length => t.val) hv
  · intro z
    have hz : z ∈ zs := by simp [zs]
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hz
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    simpa [componentOwner, zs] using hj

noncomputable def rzStepOutput_ownerLabels (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyOwnerLabels (V := Vertex (state S i.val).presentation)
      (indexedDecoderData S depth) i (rzStepOutput S depth i h sigma) :=
  AssemblyOwnerLabels.ofOwners _
    (fun j => some (.z (componentOwner S depth i h sigma j)))

theorem rzStepOutput_component_supported (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    (rzStepOutput S depth i h sigma).componentSupportAt j ⊆
      (rzData S depth i h).correctionRegion (componentOwner S depth i h sigma j) := by
  rw [AssemblyStepOutput.componentSupportAt_eq, rzStepOutput_component_eq]
  intro q hq
  by_contra hout
  have hz := localCorrectionComponent_supported (rzData S depth i h)
    (rzData_localTopCohomology S depth i h)
    (componentOwner S depth i h sigma j) sigma.val q hout
  simpa [hammingSupport, hz] using hq

theorem rzStepOutput_component_coboundary_supported (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    hammingSupport ((rzStepOutput S depth i h sigma).componentCoboundaryAt j) ⊆
      (rzData S depth i h).coarseRegion (componentOwner S depth i h sigma j) := by
  rw [AssemblyStepOutput.componentCoboundaryAt_eq, rzStepOutput_component_eq]
  intro p hp
  by_contra hout
  have hz := (rzData S depth i h).local_boundary_supported
    (componentOwner S depth i h sigma j)
    (localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h)
      (componentOwner S depth i h sigma j) sigma.val)
    (localCorrectionComponent_supported (rzData S depth i h)
      (rzData_localTopCohomology S depth i h)
      (componentOwner S depth i h sigma j) sigma.val) p hout
  simpa [hammingSupport, hz] using hp

/-- The recorded labels refer to exactly these proved support snapshots. -/
theorem rzStepOutput_owner_snapshot (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).owner =
        some (.z (componentOwner S depth i h sigma j)) ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport =
        (rzStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport =
        hammingSupport ((rzStepOutput S depth i h sigma).componentCoboundaryAt j) :=
  ⟨rfl, rfl, rfl⟩

/-- The actual selected map sends a valid lower syndrome to a valid upper one. -/
noncomputable def embeddedSyndrome
    (sigma : (indexedFamily S depth).Syndrome i.castSucc) :
    (indexedFamily S depth).Syndrome i.succ :=
  ((indexedDecoderData S depth).selectedMap i).mapSyndrome sigma

theorem rzStepOutput_map2_coarse (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.castSucc) :
    (rzStepOutput S depth i h (embeddedSyndrome S depth i sigma)).coarse = sigma := by
  apply Subtype.ext
  funext z
  rw [rzStepOutput_coarse_apply]
  change topParity (rzData S depth i h)
    (((indexedDecoderData S depth).selectedMap i).map2 sigma.val) z = sigma.val z
  rw [selectedMap_eq]
  exact congrFun (topParity_rzMap_map2 (rzData S depth i h) sigma.val) z

/-- Zero residual on a selected image is proved before discussing its selector. -/
theorem rzData_map2_residual_zero (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.castSucc)
    (z : (state S i.val).presentation.Z) :
    localResidual (rzData S depth i h) z
      (((indexedDecoderData S depth).selectedMap i).map2 sigma) = 0 := by
  have hg : EndpointResidualZero (endpointAt S depth i h) :=
    transportEndpoint_property _ _ _
      (congrArg ConstructionState.presentation (stateSuccRZ S depth i h)) _
      (fun _ G => EndpointResidualZero G)
      (actualEndpoint_residual (state S i.val).presentation (state S i.val).admissible S)
  rw [selectedMap_eq]
  change maskWord ((endpointAt S depth i h).region z)
    ((indexedEdgeMap S depth i).map2 sigma) +
    (endpointAt S depth i h).lift z
      (∑ p ∈ (endpointAt S depth i h).region z, (indexedEdgeMap S depth i).map2 sigma p) = 0
  rw [← endpointAt_map2 S depth i h]
  exact hg sigma z

/-- The canonical selector may return a cycle; its coboundary is zero. -/
theorem rzStepOutput_map2_component_boundary_zero (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.castSucc)
    (j : Fin (rzStepOutput S depth i h
      (embeddedSyndrome S depth i sigma)).localComponents.length) :
    (rzStepOutput S depth i h (embeddedSyndrome S depth i sigma)).componentCoboundaryAt j = 0 := by
  rw [AssemblyStepOutput.componentCoboundaryAt_eq, rzStepOutput_component_eq]
  funext p
  rw [localCorrectionComponent_boundary]
  exact congrFun (rzData_map2_residual_zero S depth i h sigma.val _) p

end QEC.Coding.BDL26RZDecoderAdapter


/-! ## Canonical RZ output on one literal materialized edge

This two-carrier interface instantiates the existing canonical RZ algorithm.
It supplies neither a decoder oracle nor an abstract substitute for the
actual indexed family. The physical dual tower transports this output once.
-/
noncomputable section
namespace QEC.Coding.BDL26RZDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators

def presentationAt (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rzReplacementPresentation P A.toTannerSquareAdmissible S)

abbrev PresentationX (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).X
abbrev PresentationQ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).Q
abbrev PresentationZ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).Z

def presentationFamily (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : BDL26CochainFamily 1
      (PresentationX P A S) (PresentationQ P A S) (PresentationZ P A S) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (presentationAt P A S i)

theorem presentationFamily_coboundary0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A S).coboundary0 i = tannerCoboundary0 (presentationAt P A S i) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q

theorem presentationFamily_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A S).coboundary1 i = tannerCoboundary1 (presentationAt P A S i) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z

def presentationMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : BDL26CochainMap (presentationFamily P A S) (0 : StepIndex 1) where
  map0 := rzMap0Coord P S
  map1 := map1Coord P A S
  map2 := map2Coord P A S
  commutes_coboundary0 := by
    rw [presentationFamily_coboundary0,presentationFamily_coboundary0]
    exact rzMap_commutes_coboundary0 P A S
  commutes_coboundary1 := by
    rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
    exact rzMap_commutes_coboundary1 P A S

def presentationDecoderData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) : BDL26DecoderData 1
      (PresentationX P A S) (PresentationQ P A S) (PresentationZ P A S) where
  family := presentationFamily P A S
  rxMap := fun i => Fin.cases (presentationMap P A S) (fun j => Fin.elim0 j) i
  rzMap := fun i => Fin.cases (presentationMap P A S) (fun j => Fin.elim0 j) i

@[simp] theorem presentationDecoderData_selectedMap (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (presentationDecoderData P A S).selectedMap (0 : StepIndex 1) =
      presentationMap P A S := rfl

/-- Every field comes from the actual generic endpoint construction above. -/
def presentationData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZCoarseGrainingData (presentationDecoderData P A S)
      (0 : StepIndex 1) (Vertex P) := by
  let G := actualEndpoint P A S
  refine
    { levelGraph := tannerLevel P
      center := Vertex.z
      topCenter := G.topCenter
      correctionOwner := G.owner
      coarseRegion := G.region
      correctionInputRegion := G.region
      correctionRegion := G.corrections
      lift := G.lift
      induced := ⟨G.projection⟩
      coarseRegion_cover := G.cover
      coarseRegion_disjoint := G.disjoint
      correctionInputRegion_subset := fun _ => Finset.Subset.refl _
      correctionRegion_disjoint := G.corrections_disjoint
      correctionRegion_coherence := G.coherence
      lift_supported := G.lift_supported
      lift_parity := G.lift_parity
      induced_syndrome_decomposition := ?_
      local_boundary_supported := ?_
      topRegion_radius_two := ?_
      correctionInput_radius_one := ?_ }
  · intro sigma
    exact G.decomposition sigma
  · intro z f hf p hp
    change ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) f p = 0
    rw [presentationFamily_coboundary1]
    exact G.boundary_supported z f hf p hp
  · intro z p hp
    exact (G.radius z p hp).le.trans (by decide)
  · intro z p hp
    exact (G.radius z p hp).le.trans (by decide)

theorem presentationData_localTopCohomology (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    LocalTopCohomologyIdentification (presentationData P A S) := by
  have hb (z : P.Z) :
      localBoundaryMap (presentationData P A S) z = endpointBoundary (actualEndpoint P A S) z := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) f.1 =
      tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S) f.1
    rw [presentationFamily_coboundary1]
    rfl
  intro z
  change ∃ e : ((supportedSubmodule ((actualEndpoint P A S).region z)) ⧸
      LinearMap.range (localBoundaryMap (presentationData P A S) z)) ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (localBoundaryMap (presentationData P A S) z)).mkQ r) =
      ∑ p ∈ (actualEndpoint P A S).region z, r.1 p
  rw [hb z]
  exact actualEndpoint_F07 P A S z

theorem presentationData_inducedCoboundaryCompatibility (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    InducedCoboundaryCompatibility (presentationData P A S) := by
  intro e
  change (fun z => ∑ p ∈ (actualEndpoint P A S).region z,
    ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) e p) =
    ((presentationFamily P A S).coboundary1 (0 : LevelIndex 1))
      ((actualEndpoint P A S).projection e)
  rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
  exact actualEndpoint_F09 P A S e

/-- The original canonical local functions, not an independently chosen decoder. -/
def presentationOutput (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    AssemblyStepOutput (presentationDecoderData P A S) (0 : StepIndex 1) := by
  let G := presentationData P A S
  let hc := presentationData_localTopCohomology P A S
  let hi := presentationData_inducedCoboundaryCompatibility P A S
  let coarse := coarseSyndrome G hi sigma
  let correction := correctionFromSyndrome G hc sigma.val
  let pieces := (Finset.univ : Finset P.Z).toList.map
    (fun z => localCorrectionComponent G hc z sigma.val)
  apply AssemblyStepOutput.ofComponents sigma coarse correction pieces
  · exact rz_exact_relation_selected G hc hi rfl sigma
  · exact ((localComputabilityCertificate G hc hi).totalCorrectionDecomposition sigma.val).trans
      (Finset.sum_map_toList (Finset.univ : Finset P.Z)
        (fun z : P.Z => localCorrectionComponent G hc z sigma.val)).symm

@[simp] theorem presentationOutput_correction (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).correction =
      correctionFromSyndrome (presentationData P A S)
        (presentationData_localTopCohomology P A S) sigma.val := rfl

@[simp] theorem presentationOutput_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).coarse =
      coarseSyndrome (presentationData P A S)
        (presentationData_inducedCoboundaryCompatibility P A S) sigma := rfl

@[simp] theorem presentationOutput_components (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).localComponents =
      (Finset.univ : Finset P.Z).toList.map
        (fun z => localCorrectionComponent (presentationData P A S)
          (presentationData_localTopCohomology P A S) z sigma.val) := rfl

end QEC.Coding.BDL26RZDecoderAdapter
end

namespace QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
/-- Actual parity aggregation sends zero input to zero coarse syndrome. -/
theorem presentationOutput_zero_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1))
    (hs : sigma.val = 0) : (presentationOutput P A S sigma).coarse.val = 0 := by
  rw [presentationOutput_coarse]
  funext z
  simp [coarseSyndrome,topParity,hs]
end QEC.Coding.BDL26RZDecoderAdapter
