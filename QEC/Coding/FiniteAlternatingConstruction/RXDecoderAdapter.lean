import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Decomposition
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Coordinates
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Flow
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Lifts
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Representative
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Graph
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Sectors
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Induced
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Budgets
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.LocalComplexes

import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder

/-! # Actual indexed RX decoder adapter

The adapter constructs all local data from actual replacement geometry and
uses the canonical RX decoder. Ordered pieces retain all owner labels; their
boundaries include the actual X-to-Q and Q-to-Z connecting terms.
-/
namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators

/-- Only the upper presentation varies under the defining successor transport. -/
private structure EndpointData (P U : TannerSquarePresentation) (S : OddScale) where
  lx : LocalComplexData P.X U.Z U.Q
  lq : LocalComplexData P.Q U.Z U.Q
  lz : LocalComplexData P.Z U.Z U.Q
  cx : ∀ x : P.X, ChainComplexData BDL26Field
    (Word BDL26Field (DoubleCylinderVertex P x S))
    (Word BDL26Field (LocalRegionIndex (lx.correctionRegion x)))
    (Word BDL26Field (LocalRegionIndex (lx.syndromeRegion x)))
  cq : ∀ q : P.Q, ChainComplexData BDL26Field (Word BDL26Field (Fin 0))
    (Word BDL26Field (LocalRegionIndex (lq.correctionRegion q)))
    (Word BDL26Field (LocalRegionIndex (lq.syndromeRegion q)))
  cxExact : ∀ x, LinearMap.ker (wordLinearMapTranspose (cx x).boundary2) =
    LinearMap.range (wordLinearMapTranspose (cx x).boundary1)
  cqFinrank : ∀ q, Module.finrank BDL26Field (cq q).middleCohomology = 1
  xFlow : ∀ x, Word BDL26Field (LocalRegionIndex (lx.correctionRegion x)) →ₗ[BDL26Field]
    Word BDL26Field U.Z
  qFlow : ∀ q, Word BDL26Field (LocalRegionIndex (lq.correctionRegion q)) →ₗ[BDL26Field]
    Word BDL26Field U.Z
  xLift : ∀ x, Word BDL26Field (DoubleCylinderVertex P x S) →ₗ[BDL26Field] Word BDL26Field U.X
  xRestriction : ∀ x e,
    restrictWordLinear (lx.syndromeRegion x) (tannerCoboundary1 U e) =
      wordLinearMapTranspose (cx x).boundary2 (restrictWordLinear (lx.correctionRegion x) e)
  qRestriction : ∀ q e, (∀ x, restrictWordLinear (lx.correctionRegion x) e = 0) →
    restrictWordLinear (lq.syndromeRegion q) (tannerCoboundary1 U e) =
      wordLinearMapTranspose (cq q).boundary2 (restrictWordLinear (lq.correctionRegion q) e)
  xLiftRestriction : ∀ x s,
    restrictWordLinear (lx.correctionRegion x) (tannerCoboundary0 U (xLift x s)) =
      wordLinearMapTranspose (cx x).boundary1 s
  xLiftSum : ∀ (s : ∀ x, Word BDL26Field (DoubleCylinderVertex P x S)) x,
    restrictWordLinear (lx.correctionRegion x) (tannerCoboundary0 U (∑ y, xLift y (s y))) =
      wordLinearMapTranspose (cx x).boundary1 (s x)
  qDelta0Zero : ∀ q, wordLinearMapTranspose (cq q).boundary1 = 0
  xDecomposition : ∀ x f,
    tannerCoboundary1 U (extendWordLinear (lx.correctionRegion x) f) =
      extendWordLinear (lx.syndromeRegion x) (wordLinearMapTranspose (cx x).boundary2 f) + xFlow x f
  qDecomposition : ∀ q f,
    tannerCoboundary1 U (extendWordLinear (lq.correctionRegion q) f) =
      extendWordLinear (lq.syndromeRegion q) (wordLinearMapTranspose (cq q).boundary2 f) + qFlow q f
  xBudget : ∀ x s, s ∈ LinearMap.range (wordLinearMapTranspose (cx x).boundary2) →
    ∃ f, wordLinearMapTranspose (cx x).boundary2 f = s ∧ HammingWeight (xFlow x f) ≤ HammingWeight s
  qBudget : ∀ q s, s ∈ LinearMap.range (wordLinearMapTranspose (cq q).boundary2) →
    ∃ f, wordLinearMapTranspose (cq q).boundary2 f = s ∧ HammingWeight (qFlow q f) ≤ HammingWeight s
  xs : Finset U.Z
  qs : Finset U.Z
  zs : Finset U.Z
  xsRegions : xs = rxRegionUnion lx
  qsRegions : qs = rxRegionUnion lq
  zsRegions : zs = rxRegionUnion lz
  sectorsDisjoint : Disjoint xs qs ∧ Disjoint xs zs ∧ Disjoint qs zs
  sectorsCover : xs ∪ qs ∪ zs = Finset.univ
  qcs : Finset U.Q
  qcsRegions : qcs = correctionRegionUnion lq
  correctionsCover : correctionRegionUnion lx ∪ qcs = Finset.univ
  correctionsDisjoint : Disjoint (correctionRegionUnion lx) qcs
  xFlowZeroX : ∀ x f p, p ∈ xs → xFlow x f p = 0
  qFlowZeroQ : ∀ q f p, p ∈ qs → qFlow q f p = 0
  qFlowZeroX : ∀ q f p, p ∈ xs → qFlow q f p = 0
  xSyndromeDisjoint : ∀ x y, x ≠ y → Disjoint (lx.syndromeRegion x) (lx.syndromeRegion y)
  qSyndromeDisjoint : ∀ q r, q ≠ r → Disjoint (lq.syndromeRegion q) (lq.syndromeRegion r)
  zSyndromeDisjoint : ∀ z w, z ≠ w → Disjoint (lz.syndromeRegion z) (lz.syndromeRegion w)
  xCorrectionDisjoint : ∀ x y, x ≠ y → Disjoint (lx.correctionRegion x) (lx.correctionRegion y)
  qCorrectionDisjoint : ∀ q r, q ≠ r → Disjoint (lq.correctionRegion q) (lq.correctionRegion r)
  xqCorrectionDisjoint : ∀ x q, Disjoint (lx.correctionRegion x) (lq.correctionRegion q)
  zCorrectionEmpty : ∀ z, lz.correctionRegion z = ∅
  representative : ∀ q, (cq q).middleCohomology →ₗ[BDL26Field] (cq q).middleCocycleCode.carrier
  representativeSection : ∀ q h, (cq q).middleCoboundaryInCocycles.mkQ (representative q h) = h
  representativeSupport : ∀ q h p, p.1 ∉ qcs → (representative q h).1 p = 0
  quotientEquiv : (∀ q, (cq q).middleCohomology) ≃ₗ[BDL26Field] Word BDL26Field P.Q
  map0 : Word BDL26Field P.X →ₗ[BDL26Field] Word BDL26Field U.X
  map1 : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field U.Q
  map2 : Word BDL26Field P.Z →ₗ[BDL26Field] Word BDL26Field U.Z
  map1Representative : ∀ w, map1 w = ∑ q, extendWordLinear (lq.correctionRegion q)
    (representative q (quotientEquiv.symm w q)).1
  pairEquiv : (P.Z × Fin 2) ≃ LocalRegionIndex zs
  map2Diagonal : ∀ w z b, map2 w (pairEquiv (z,b)).1 = w z
  map2Auxiliary : ∀ w p, p ∉ zs → map2 w p = 0
  topCenter : U.Z → RXVertex P.X P.Q P.Z
  correctionOwner : U.Q → RXVertex P.X P.Q P.Z
  centerX : ∀ x p, p ∈ lx.syndromeRegion x ↔ topCenter p = .inl x
  centerQ : ∀ q p, p ∈ lq.syndromeRegion q ↔ topCenter p = .inr (.inl q)
  centerZ : ∀ z p, p ∈ lz.syndromeRegion z ↔ topCenter p = .inr (.inr z)
  ownerX : ∀ x p, p ∈ lx.correctionRegion x ↔ correctionOwner p = .inl x
  ownerQ : ∀ q p, p ∈ lq.correctionRegion q ↔ correctionOwner p = .inr (.inl q)
  ownerZ : ∀ z p, p ∈ lz.correctionRegion z ↔ correctionOwner p = .inr (.inr z)
  centerPair : ∀ z b, topCenter (pairEquiv (z,b)).1 = .inr (.inr z)
  xRadius : ∀ x f p, xFlow x f p ≠ 0 →
    DirectedGraph.distance (rxLevel P).graph (.inl x) (topCenter p) ≤ 1
  qRadius : ∀ q f p, qFlow q f p ≠ 0 →
    DirectedGraph.distance (rxLevel P).graph (.inr (.inl q)) (topCenter p) ≤ 1

-- Every field is constructed from actual replacement geometry below.
-- No public constructor accepts an endpoint certificate.

private theorem relabel_fiber_iff (P : TannerSquarePresentation)
    {C : Type} [Fintype C] [DecidableEq C] (owner : C → Vertex P)
    (v : RXVertex P.X P.Q P.Z) (p : C) :
    p ∈ fiberRegion owner (vertexEquiv P v) ↔ (vertexEquiv P).symm (owner p) = v := by
  constructor
  · intro hp
    have h := (Finset.mem_filter.mp hp).2
    rw [h, Equiv.symm_apply_apply]
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_⟩
    have h := congrArg (vertexEquiv P) hp
    simpa only [Equiv.apply_symm_apply] using h

private theorem actualZ_decEq (P : TannerSquarePresentation) (S : OddScale) :
    (rxReplacementPresentation P S).data.zDecidableEq =
      (inferInstance : DecidableEq (RX2 P S)) := Subsingleton.elim _ _

private theorem extendWordLinear_decEq {T : Type} [Fintype T]
    (d e : DecidableEq T) (Y : Finset T) (f : Word BDL26Field (LocalRegionIndex Y)) :
    @extendWordLinear BDL26Field _ T _ d Y f = @extendWordLinear BDL26Field _ T _ e Y f := by
  cases Subsingleton.elim d e
  rfl

private noncomputable def actualEndpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointData P (rxReplacementPresentation P S) S where
  lx := ⟨(localX P S).syndromeRegion, (localX P S).correctionRegion⟩
  lq := ⟨(localQ P S).syndromeRegion, (localQ P S).correctionRegion⟩
  lz := ⟨(localZ P S).syndromeRegion, (localZ P S).correctionRegion⟩
  cx := localCx P S
  cq := localCq P S
  cxExact := localCx_exact P A.toTannerSquareAdmissibleV3 R S
  cqFinrank := localCq_finrank P A.toTannerSquareAdmissible S
  xFlow := fun x => (xFlow P S x).comp (wordEquiv (xCorrectionEquiv P S x)).symm.toLinearMap
  qFlow := fun q => (qFlow P S q).comp (wordEquiv (qCorrectionEquiv P S q)).symm.toLinearMap
  xLift := xLift P S
  xRestriction := by
    intro x e
    rw [rxPresentation_coboundary1_eq P A R S]
    exact localCx_global_restriction P S e x
  qRestriction := by
    intro q e hx
    rw [rxPresentation_coboundary1_eq P A R S]
    exact localCq_global_restriction P S e hx q
  xLiftRestriction := by
    intro x w
    rw [rxPresentation_coboundary0_eq P A R S]
    exact localCx_lift_restriction P S x w
  xLiftSum := by
    intro w x
    rw [rxPresentation_coboundary0_eq P A R S]
    exact localCx_lift_sum_restriction P S w x
  qDelta0Zero := localCq_delta0_zero P S
  xDecomposition := by
    intro x f
    rw [rxPresentation_coboundary1_eq P A R S]
    exact (localCx_decomposition P S x f).trans
      (congrArg (fun w => w + xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f))
        (extendWordLinear_decEq _ _ _ _))
  qDecomposition := by
    intro q f
    rw [rxPresentation_coboundary1_eq P A R S]
    exact (localCq_decomposition P S q f).trans
      (congrArg (fun w => w + qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f))
        (extendWordLinear_decEq _ _ _ _))
  xBudget := localCx_budget P A R S
  qBudget := localCq_budget P S
  xs := xSector P S
  qs := qSector P S
  zs := zSector P S
  xsRegions := by
    rw [actualZ_decEq]
    exact xSector_regions P S
  qsRegions := by
    rw [actualZ_decEq]
    exact qSector_regions P S
  zsRegions := by
    rw [actualZ_decEq]
    exact zSector_regions P S
  sectorsDisjoint := syndrome_sectors_disjoint P S
  sectorsCover := by
    rw [actualZ_decEq]
    exact syndrome_sectors_cover P S
  qcs := qCorrectionSector P S
  qcsRegions := qCorrectionSector_regions P S
  correctionsCover := correction_sectors_cover P S
  correctionsDisjoint := correction_sectors_disjoint P S
  xFlowZeroX := by
    intro x f p hp
    obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨z,a⟩ | ⟨q,e⟩) | ⟨z,c⟩
    · exact xFlow_at_x P S x z _ a
    · cases hy
    · cases hy
  qFlowZeroQ := by
    intro q f p hp
    obtain ⟨r,hr⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨x,a⟩ | ⟨s,e⟩) | ⟨z,c⟩
    · cases hr
    · exact qFlow_at_q P S q s _ e
    · cases hr
  qFlowZeroX := by
    intro q f p hp
    obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨x,a⟩ | ⟨s,e⟩) | ⟨z,c⟩
    · exact qFlow_at_x P S q _ x a
    · cases hy
    · cases hy
  xSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.x.inj he))
  qSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.q.inj he))
  zSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.z.inj he))
  xCorrectionDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.x.inj he))
  qCorrectionDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.q.inj he))
  xqCorrectionDisjoint := fun x q => fiberRegion_disjoint (rxCorrectionOwner P S)
    (first := Vertex.x x) (second := Vertex.q q) (by intro he; cases he)
  zCorrectionEmpty := z_correction_empty P S
  representative := qRepresentative P A.toTannerSquareAdmissible S
  representativeSection := qRepresentative_section P A.toTannerSquareAdmissible S
  representativeSupport := by
    intro q h p hp
    apply (hp ?_).elim
    apply Finset.mem_filter.mpr
    have ho := (relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inl q)) p.1).mp p.2
    have he : rxCorrectionOwner P S p.1 = Vertex.q q := by
      apply (vertexEquiv P).symm.injective
      exact ho
    exact ⟨Finset.mem_univ _, q, he⟩
  quotientEquiv := qCohomologyEquiv P A.toTannerSquareAdmissible S
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S
  map1Representative := map1_representative_decomposition P A.toTannerSquareAdmissible S
  pairEquiv := zPairEquiv P S
  map2Diagonal := map2_diagonal P S
  map2Auxiliary := map2_auxiliary_zero P S
  topCenter := topCenter P S
  correctionOwner := fun p => (vertexEquiv P).symm (rxCorrectionOwner P S p)
  centerX := fun x p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inl x) p
  centerQ := fun q p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inr (.inl q)) p
  centerZ := fun z p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inr (.inr z)) p
  ownerX := fun x p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inl x) p
  ownerQ := fun q p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inl q)) p
  ownerZ := fun z p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inr z)) p
  centerPair := fun _ _ => rfl
  xRadius := fun x f p hp => xFlow_radius_one P A.toTannerSquareAdmissible S x _ p hp
  qRadius := fun q f p hp => qFlow_radius_one P S q _ p hp

open BDL26IndexedDecoder BDL26AlternatingCochain

private def transportEndpoint (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) : EndpointData P U S := h.symm ▸ G

private theorem transportEndpoint_maps (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) :
    HEq (transportEndpoint P U V S h G).map0 G.map0 ∧
    HEq (transportEndpoint P U V S h G).map1 G.map1 ∧
    HEq (transportEndpoint P U V S h G).map2 G.map2 := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

private theorem stateSuccRX (h : i.val % 2 = 0) :
    state S (i.val + 1) = rxState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_pos h

private noncomputable def endpointAt (h : i.val % 2 = 0) :
    EndpointData (state S i.val).presentation (state S (i.val + 1)).presentation S :=
  transportEndpoint _ _ _ S (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)

private theorem endpointAt_maps (h : i.val % 2 = 0) :
    (endpointAt S depth i h).map0 = (indexedEdgeMap S depth i).map0 ∧
    (endpointAt S depth i h).map1 = (indexedEdgeMap S depth i).map1 ∧
    (endpointAt S depth i h).map2 = (indexedEdgeMap S depth i).map2 := by
  have hf := transportEndpoint_maps _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  have hm := indexedDecoderData_selected_rx S depth i h
  rw [selectedMap_eq] at hm
  exact ⟨eq_of_heq (hf.1.trans hm.1.symm),
    eq_of_heq (hf.2.1.trans hm.2.1.symm), eq_of_heq (hf.2.2.trans hm.2.2.symm)⟩

/-- Actual upper owner fibres, transported along the defining RX successor. -/
noncomputable def rxLx (h : i.val % 2 = 0) := (endpointAt S depth i h).lx
noncomputable def rxLq (h : i.val % 2 = 0) := (endpointAt S depth i h).lq
noncomputable def rxLz (h : i.val % 2 = 0) := (endpointAt S depth i h).lz

private noncomputable def localComplexesAt (h : i.val % 2 = 0) :
    RXLocalComplexData
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) where
  cx := (endpointAt S depth i h).cx
  cq := (endpointAt S depth i h).cq
  cz := rxCz (state S i.val).presentation

private theorem decoder_coboundary0 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary0 j =
      tannerCoboundary0 (state S j.val).presentation := indexedFamily_coboundary0 S depth j

private theorem decoder_coboundary1 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      tannerCoboundary1 (state S j.val).presentation := indexedFamily_coboundary1 S depth j

private noncomputable def supportAt (h : i.val % 2 = 0) :
    RXSupportDecomposition (indexedDecoderData S depth) i (localComplexesAt S depth i h) := by
  let G := endpointAt S depth i h
  refine
    { cxFlow := G.xFlow
      cqFlow := G.qFlow
      cxLift0 := G.xLift
      cqLift0 := fun _ => 0
      cxDelta1_restriction := ?_
      cxDelta1_restriction_global := ?_
      cqDelta1_restriction := ?_
      cqDelta1_restriction_global := ?_
      cxDelta0_restriction := ?_
      cxDelta0_sum_decomposition := ?_
      cxDelta1_decomposition := ?_
      cqDelta1_decomposition := ?_
      cxFlow_outside_x_sector := ?_
      cqFlow_outside_q_sector := ?_
      cx_regions_pairwise_disjoint := G.xSyndromeDisjoint
      cq_regions_pairwise_disjoint := G.qSyndromeDisjoint }
  · intro x f
    have hr := G.xRestriction x (extendWordLinear (G.lx.correctionRegion x) f)
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x)
      (d (extendWordLinear (G.lx.correctionRegion x) f)))
      (decoder_coboundary1 S depth i.succ)).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cx x).boundary2)
          (region_restrict_extend (G.lx.correctionRegion x) f)))
  · intro x e
    rw [decoder_coboundary1]
    exact G.xRestriction x e
  · intro q f
    have hr := G.qRestriction q (extendWordLinear (G.lq.correctionRegion q) f)
      (fun x => region_restrict_extend_disjoint _ _ (G.xqCorrectionDisjoint x q).symm f)
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q)
      (d (extendWordLinear (G.lq.correctionRegion q) f)))
      (decoder_coboundary1 S depth i.succ)).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cq q).boundary2)
          (region_restrict_extend (G.lq.correctionRegion q) f)))
  · intro q e hx
    rw [decoder_coboundary1]
    exact G.qRestriction q e hx
  · intro x s
    rw [decoder_coboundary0]
    exact G.xLiftRestriction x s
  · intro s x
    rw [decoder_coboundary0]
    exact G.xLiftSum s x
  · intro x f
    rw [decoder_coboundary1]
    exact G.xDecomposition x f
  · intro q f
    rw [decoder_coboundary1]
    exact G.qDecomposition q f
  · intro x f p hp
    exact G.xFlowZeroX x f p (G.xsRegions.symm ▸ hp)
  · intro q f p hp
    exact G.qFlowZeroQ q f p (G.qsRegions.symm ▸ hp)

/-- Actual F04/F06/F11/F12 contract, with no caller-supplied proof certificate. -/
noncomputable def rxContract (h : i.val % 2 = 0) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) where
  rx_local_complexes := localComplexesAt S depth i h
  rx_local_cohomology :=
    { cx_h1_ker_eq_range := (endpointAt S depth i h).cxExact
      cq_h1_finrank := (endpointAt S depth i h).cqFinrank }
  support_decomposition := supportAt S depth i h
  local_boundary_weight_budgets :=
    { cx := (endpointAt S depth i h).xBudget
      cq := (endpointAt S depth i h).qBudget }

private noncomputable def representativeAt (h : i.val % 2 = 0) (q : (state S i.val).presentation.Q) :
    ((rxContract S depth i h).rx_local_complexes.cq q).middleCohomology →ₗ[BDL26Field]
      ((rxContract S depth i h).rx_local_complexes.cq q).middleCocycleCode.carrier :=
  (endpointAt S depth i h).representative q

private theorem representativeAt_section (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) (v) :
    ((rxContract S depth i h).rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
      (representativeAt S depth i h q v) = v :=
  (endpointAt S depth i h).representativeSection q v

private theorem representativeAt_support (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) (v)
    (p : LocalRegionIndex ((rxLq S depth i h).correctionRegion q))
    (hp : p.1 ∉ (endpointAt S depth i h).qcs) :
    (representativeAt S depth i h q v).1 p = 0 :=
  (endpointAt S depth i h).representativeSupport q v p hp

private noncomputable def quotientEquivAt (h : i.val % 2 = 0) :
    (∀ q, ((rxContract S depth i h).rx_local_complexes.cq q).middleCohomology) ≃ₗ[BDL26Field]
      (indexedDecoderData S depth).family.Cochain1 i.castSucc :=
  (endpointAt S depth i h).quotientEquiv

/-- Actual indexed RX coarse-graining data in every even-lower-index step. -/
noncomputable def rxData (h : i.val % 2 = 0) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) := by
  let P := (state S i.val).presentation
  let A := (state S i.val).admissible.toTannerSquareAdmissible
  let G := endpointAt S depth i h
  refine
    { induced :=
        { adjacencyMap := rxXQAdjacency P
          gXQ0 := actualGXQ0 P A S
          gXQ0_eq_adjacency := actualGXQ0_eq_adjacency P A S
          qzAdjacency := rxQZAdjacency P
          gQZ1 := actualGQZ1 P S
          gQZ1_eq_diagonal_comp := actualGQZ1_eq_diagonal P A S
          zSector := G.zs
          zPairEquiv := G.pairEquiv
          map2_diagonal := ?_
          map2_auxiliary_zero := ?_ }
      contract := rxContract S depth i h
      xSector := G.xs
      qSector := G.qs
      zSector := G.zs
      zSector_eq_induced := rfl
      xSector_eq_regions := G.xsRegions
      qSector_eq_regions := G.qsRegions
      sectors_pairwise_disjoint := G.sectorsDisjoint
      sectors_cover := G.sectorsCover
      qCorrectionSector := G.qcs
      qCorrectionSector_eq_regions := G.qcsRegions
      correction_sectors_cover := G.correctionsCover
      correction_sectors_disjoint := G.correctionsDisjoint
      qRepresentativeSector := G.qcs
      qRepresentativeSector_subset_qCorrectionSector := Finset.Subset.refl _
      cqRepresentative := representativeAt S depth i h
      cqRepresentative_mkQ := representativeAt_section S depth i h
      cqRepresentative_supported := representativeAt_support S depth i h
      qCohomologyEquiv := quotientEquivAt S depth i h
      rxMap1_eq_cqRepresentative := ?_
      cqDelta0_sum_decomposition := ?_
      cqFlow_outside_xSector := G.qFlowZeroX
      levelGraph := rxLevel P
      levelGraph_kind_x := fun _ => rfl
      levelGraph_kind_q := fun _ => rfl
      levelGraph_kind_z := fun _ => rfl
      topCenter := G.topCenter
      coarseCenter := fun z => .inr (.inr z)
      coarseCenter_is_z := fun z => ⟨z,rfl⟩
      topCenter_coarse_pair := G.centerPair
      topCenter_x_iff := G.centerX
      topCenter_q_iff := G.centerQ
      topCenter_z_iff := G.centerZ
      zSector_eq_regions := G.zsRegions
      lz_regions_pairwise_disjoint := G.zSyndromeDisjoint
      cx_correction_regions_pairwise_disjoint := G.xCorrectionDisjoint
      cq_correction_regions_pairwise_disjoint := G.qCorrectionDisjoint
      cxFlow_radius_one := G.xRadius
      cqFlow_radius_one := G.qRadius
      distance_one_comp := distance_one_comp _ }
  · intro w z b
    change (indexedEdgeMap S depth i).map2 w (G.pairEquiv (z,b)).1 = w z
    rw [← (endpointAt_maps S depth i h).2.2]
    exact G.map2Diagonal w z b
  · intro w p hp
    change (indexedEdgeMap S depth i).map2 w p = 0
    rw [← (endpointAt_maps S depth i h).2.2]
    exact G.map2Auxiliary w p hp
  · intro w
    change (indexedEdgeMap S depth i).map1 w = _
    rw [← (endpointAt_maps S depth i h).2.1]
    exact G.map1Representative w
  · intro s
    change (indexedFamily S depth).coboundary0 i.succ (∑ q, (0 : _ →ₗ[BDL26Field] _) (s q)) =
      ∑ q, extendWordLinear (G.lq.correctionRegion q) (wordLinearMapTranspose (G.cq q).boundary1 (s q))
    simp only [LinearMap.zero_apply, Finset.sum_const_zero, map_zero, G.qDelta0Zero]

open RXCoarseGrainingData

private theorem upper_odd (h : i.val % 2 = 0) : i.succ.val % 2 = 1 := by
  change (i.val + 1) % 2 = 1
  omega

/-- The existing canonical RX decoder on the actual indexed geometry. -/
noncomputable def rxStepOutput (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  AuditedLeafAdapters.rxOutput (rxData S depth i h) (upper_odd depth i h) sigma

theorem rxStepOutput_assembly_relation (h : i.val % 2 = 0) :
    AssemblyStepRelation (indexedDecoderData S depth) i (rxStepOutput S depth i h) :=
  AuditedLeafAdapters.rxOutput_relation (rxData S depth i h) (upper_odd depth i h)

theorem rxStepOutput_relation (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigma.val = (indexedFamily S depth).coboundary1 i.succ
      (rxStepOutput S depth i h sigma).correction +
      ((indexedDecoderData S depth).selectedMap i).map2
        (rxStepOutput S depth i h sigma).coarse.val :=
  (rxStepOutput S depth i h sigma).relation

theorem rxStepOutput_weight (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    2 * HammingWeight (rxStepOutput S depth i h sigma).coarse.val ≤ HammingWeight sigma.val :=
  AuditedLeafAdapters.rxOutput_weight _ _ _

theorem rxStepOutput_coarse (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).coarse.val = rxCoarseWord (rxData S depth i h) sigma.val := by
  let hs := rx_coarse_graining_odd (rxData S depth i h) (upper_odd depth i h) sigma
  exact (Classical.choose_spec (Classical.choose_spec hs)).1

theorem rxStepOutput_correction (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).correction = rxCorrectionTotal (rxData S depth i h) sigma.val := by
  let hs := rx_coarse_graining_odd (rxData S depth i h) (upper_odd depth i h) sigma
  exact (Classical.choose_spec (Classical.choose_spec hs)).2.1

theorem rxStepOutput_correction_sum (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).correction =
      (∑ x, cxComponentTotal (rxData S depth i h) sigma.val x) +
      ∑ q, cqComponentTotal (rxData S depth i h) sigma.val q := by
  rw [rxStepOutput_correction]
  exact rx_total_eq_components _ _

/-- This is the exact enumeration used inside the canonical output. -/
noncomputable def orderedOwners : List (Vertex (state S i.val).presentation) :=
  (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
      (vertexEquiv (state S i.val).presentation)

theorem orderedOwners_nodup : (orderedOwners S depth i).Nodup :=
  List.Nodup.map (vertexEquiv _).injective (Finset.nodup_toList _)

theorem orderedOwners_coverage (v : Vertex (state S i.val).presentation) :
    v ∈ orderedOwners S depth i := by
  apply List.mem_map.mpr
  exact ⟨(vertexEquiv _).symm v, by simp, Equiv.apply_symm_apply _ _⟩

theorem rxStepOutput_localComponents (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).localComponents =
      (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
        (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
          (fun v => (rxLocalComponents (rxData S depth i h)).component v sigma.val) := rfl

theorem orderedOwners_length (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (orderedOwners S depth i).length = (rxStepOutput S depth i h sigma).localComponents.length := by
  simp only [orderedOwners, rxStepOutput_localComponents, List.length_map]

noncomputable def componentOwner (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z :=
  (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.get
      ⟨j.val, by simpa only [rxStepOutput_localComponents, List.length_map] using j.isLt⟩

theorem rxStepOutput_component_eq (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    (rxStepOutput S depth i h sigma).componentAt j =
      (rxLocalComponents (rxData S depth i h)).component (componentOwner S depth i h sigma j) sigma.val := by
  change ((Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
      (fun v => (rxLocalComponents (rxData S depth i h)).component v sigma.val))[j.val] = _
  rw [List.getElem_map]
  rfl

theorem componentOwner_bijective (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    Function.Bijective (componentOwner S depth i h sigma) := by
  let vs := (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList
  have hlen : (rxStepOutput S depth i h sigma).localComponents.length = vs.length := by
    simp only [rxStepOutput_localComponents, List.length_map]
    rfl
  constructor
  · intro j k he
    apply Fin.ext
    have hn : vs.Nodup := Finset.nodup_toList _
    have hv := hn.get_inj_iff.mp he
    exact congrArg (fun t : Fin vs.length => t.val) hv
  · intro v
    have hv : v ∈ vs := by simp [vs]
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    simpa [componentOwner, vs] using hj

noncomputable def rxStepOutput_ownerLabels (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyOwnerLabels (V := Vertex (state S i.val).presentation)
      (indexedDecoderData S depth) i (rxStepOutput S depth i h sigma) :=
  AssemblyOwnerLabels.ofOwners _ (fun j => some
    (vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j)))

theorem rxStepOutput_owner_snapshot (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).owner =
      some (vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j)) ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport =
      (rxStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport =
      hammingSupport ((rxStepOutput S depth i h sigma).componentCoboundaryAt j) := ⟨rfl,rfl,rfl⟩

/-- Actual indexed correction owner, including the fact that no Z coordinate occurs. -/
noncomputable def correctionOwnerAt (h : i.val % 2 = 0) :=
  (endpointAt S depth i h).correctionOwner

theorem correctionOwnerAt_region (h : i.val % 2 = 0)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z)
    (p : FamilyQ S depth i.succ) :
    p ∈ (rxXiLocalComplex (rxData S depth i h)).correctionRegion v ↔
      correctionOwnerAt S depth i h p = v := by
  let G := endpointAt S depth i h
  rcases v with x | (q | z)
  · exact G.ownerX x p
  · exact G.ownerQ q p
  · change p ∈ (∅ : Finset _) ↔ G.correctionOwner p = .inr (.inr z)
    rw [← G.ownerZ, G.zCorrectionEmpty]

theorem rxLz_correction_empty (h : i.val % 2 = 0) (z : (state S i.val).presentation.Z) :
    (rxLz S depth i h).correctionRegion z = ∅ :=
  (endpointAt S depth i h).zCorrectionEmpty z

theorem rxStepOutput_component_supported (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    (rxStepOutput S depth i h sigma).componentSupportAt j ⊆
      (rxXiLocalComplex (rxData S depth i h)).correctionRegion (componentOwner S depth i h sigma j) := by
  rw [AssemblyStepOutput.componentSupportAt_eq, rxStepOutput_component_eq]
  intro p hp
  by_contra hout
  have hz := rx_component_supported (rxData S depth i h)
    (componentOwner S depth i h sigma j) sigma.val p hout
  have hn := (Finset.mem_filter.mp hp).2
  exact hn hz

theorem rxStepOutput_mask_component (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    maskWord ((rxXiLocalComplex (rxData S depth i h)).correctionRegion
      (componentOwner S depth i h sigma j)) (rxStepOutput S depth i h sigma).correction =
        (rxStepOutput S depth i h sigma).componentAt j := by
  rw [rxStepOutput_correction, rxStepOutput_component_eq,
    rx_total_correction_decomposition]
  exact rx_masked_total_correction_eq_component (rxData S depth i h)
    (componentOwner S depth i h sigma j) sigma.val

private theorem extend_restrict_supported {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (f : Word BDL26Field A) (hf : ∀ p, p ∉ Y → f p = 0) :
    extendWordLinear Y (restrictWordLinear Y f) = f := by
  funext p
  change extendLocalSignal Y (restrictWordLinear Y f) p = f p
  by_cases hp : p ∈ Y
  · simp only [extendLocalSignal, dif_pos hp]
    rfl
  · simp only [extendLocalSignal, dif_neg hp, hf p hp]

/-- The X component has its local boundary and the actual outgoing X-to-Q term. -/
theorem x_component_boundary (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (x : (state S i.val).presentation.X) :
    (indexedFamily S depth).coboundary1 i.succ (cxComponentTotal (rxData S depth i h) sigma x) =
      fun p => extendWordLinear ((rxLx S depth i h).syndromeRegion x)
        ((rxContract S depth i h).rx_local_complexes.cxDelta1 x
          (restrictWordLinear ((rxLx S depth i h).correctionRegion x)
            (cxComponentTotal (rxData S depth i h) sigma x))) p +
      (rxContract S depth i h).support_decomposition.cxFlow x
        (restrictWordLinear ((rxLx S depth i h).correctionRegion x)
          (cxComponentTotal (rxData S depth i h) sigma x)) p := by
  have he := extend_restrict_supported ((rxLx S depth i h).correctionRegion x)
    (cxComponentTotal (rxData S depth i h) sigma x)
    (cxComponentTotal_supported (rxData S depth i h) sigma x)
  exact (congrArg ((indexedFamily S depth).coboundary1 i.succ) he.symm).trans
    ((rxContract S depth i h).support_decomposition.cxDelta1_decomposition x _)


/-- The Q component has its local boundary and the actual outgoing Q-to-Z term. -/
theorem q_component_boundary (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (q : (state S i.val).presentation.Q) :
    (indexedFamily S depth).coboundary1 i.succ (cqComponentTotal (rxData S depth i h) sigma q) =
      fun p => extendWordLinear ((rxLq S depth i h).syndromeRegion q)
        ((rxContract S depth i h).rx_local_complexes.cqDelta1 q
          (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
            (cqComponentTotal (rxData S depth i h) sigma q))) p +
      (rxContract S depth i h).support_decomposition.cqFlow q
        (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
          (cqComponentTotal (rxData S depth i h) sigma q)) p := by
  have he := extend_restrict_supported ((rxLq S depth i h).correctionRegion q)
    (cqComponentTotal (rxData S depth i h) sigma q)
    (cqComponentTotal_supported (rxData S depth i h) sigma q)
  exact (congrArg ((indexedFamily S depth).coboundary1 i.succ) he.symm).trans
    ((rxContract S depth i h).support_decomposition.cqDelta1_decomposition q _)


theorem z_component_boundary (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (z : (state S i.val).presentation.Z) :
    (indexedFamily S depth).coboundary1 i.succ
      ((rxLocalComponents (rxData S depth i h)).component (.inr (.inr z)) sigma) = 0 := map_zero _

private theorem extended_outside {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (f : Word BDL26Field (LocalRegionIndex Y)) (p : A) (hp : p ∉ Y) :
    extendWordLinear Y f p = 0 := by
  change extendLocalSignal Y f p = 0
  simp only [extendLocalSignal, dif_neg hp]

/-- Component boundaries may reach an adjacent owner through the connecting flow. -/
theorem component_boundary_radius_one (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z)
    (p : FamilyZ S depth i.succ)
    (hp : (indexedFamily S depth).coboundary1 i.succ
      ((rxLocalComponents (rxData S depth i h)).component v sigma) p ≠ 0) :
    DirectedGraph.distance (rxData S depth i h).levelGraph.graph v
      ((rxData S depth i h).topCenter p) ≤ 1 := by
  let A := rxData S depth i h
  rcases v with x | (q | z)
  · by_cases hm : p ∈ (rxLx S depth i h).syndromeRegion x
    · rw [(A.topCenter_x_iff x p).mp hm]
      exact (distance_le_one_iff _ _ _).mpr (Or.inl rfl)
    · apply A.cxFlow_radius_one x
        (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (cxComponentTotal A sigma x)) p
      intro hz
      apply hp
      change (indexedFamily S depth).coboundary1 i.succ (cxComponentTotal A sigma x) p = 0
      rw [x_component_boundary S depth i h sigma x]
      change extendWordLinear _ _ p + _ = 0
      rw [extended_outside _ _ p hm, zero_add]
      exact hz
  · by_cases hm : p ∈ (rxLq S depth i h).syndromeRegion q
    · rw [(A.topCenter_q_iff q p).mp hm]
      exact (distance_le_one_iff _ _ _).mpr (Or.inl rfl)
    · apply A.cqFlow_radius_one q
        (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (cqComponentTotal A sigma q)) p
      intro hz
      apply hp
      change (indexedFamily S depth).coboundary1 i.succ (cqComponentTotal A sigma q) p = 0
      rw [q_component_boundary S depth i h sigma q]
      change extendWordLinear _ _ p + _ = 0
      rw [extended_outside _ _ p hm, zero_add]
      exact hz
  · exact (hp (congrFun (z_component_boundary S depth i h sigma z) p)).elim

theorem rxStepOutput_component_boundary_radius_one (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (p : FamilyZ S depth i.succ)
    (hp : (rxStepOutput S depth i h sigma).componentCoboundaryAt j p ≠ 0) :
    DirectedGraph.distance (rxData S depth i h).levelGraph.graph
      (componentOwner S depth i h sigma j) ((rxData S depth i h).topCenter p) ≤ 1 := by
  rw [AssemblyStepOutput.componentCoboundaryAt_eq, rxStepOutput_component_eq] at hp
  exact component_boundary_radius_one S depth i h sigma.val _ p hp

/-- Canonical readout from the first coordinate of each actual doubled Z block. -/
theorem rxStepOutput_coarse_readout (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (z : FamilyZ S depth i.castSucc) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      rxSigmaAfterCq (rxData S depth i h) sigma.val
        ((rxData S depth i h).induced.zPairEquiv (z,0)).1 := by
  rw [rxStepOutput_coarse]
  rfl

theorem orderedOwners_get (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    (orderedOwners S depth i).get ⟨j.val, by
      rw [orderedOwners_length S depth i h sigma]; exact j.isLt⟩ =
      vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j) := by
  have hj : j.val < ((Finset.univ : Finset (RXVertex (state S i.val).presentation.X
      (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
        (vertexEquiv (state S i.val).presentation)).length := by
    change j.val < (orderedOwners S depth i).length
    rw [orderedOwners_length S depth i h sigma]
    exact j.isLt
  change ((Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
      (vertexEquiv (state S i.val).presentation))[j.val]'hj = _
  rw [List.getElem_map]
  rfl

theorem rxStepOutput_component_x (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (x : (state S i.val).presentation.X)
    (hj : componentOwner S depth i h sigma j = .inl x) :
    (rxStepOutput S depth i h sigma).componentAt j = cxComponentTotal (rxData S depth i h) sigma.val x := by
  rw [rxStepOutput_component_eq, hj]
  rfl

theorem rxStepOutput_component_q (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (q : (state S i.val).presentation.Q)
    (hj : componentOwner S depth i h sigma j = .inr (.inl q)) :
    (rxStepOutput S depth i h sigma).componentAt j = cqComponentTotal (rxData S depth i h) sigma.val q := by
  rw [rxStepOutput_component_eq, hj]
  rfl

theorem rxStepOutput_component_z (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (z : (state S i.val).presentation.Z)
    (hj : componentOwner S depth i h sigma j = .inr (.inr z)) :
    (rxStepOutput S depth i h sigma).componentAt j = 0 := by
  rw [rxStepOutput_component_eq, hj]
  rfl

theorem rxStepOutput_component_sum (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).correction =
      (rxStepOutput S depth i h sigma).localComponents.sum :=
  (rxStepOutput S depth i h sigma).correction_decomposition

private theorem transportEndpoint_regions (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) :
    HEq (transportEndpoint P U V S h G).lx.syndromeRegion G.lx.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lx.correctionRegion G.lx.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).lq.syndromeRegion G.lq.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lq.correctionRegion G.lq.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).lz.syndromeRegion G.lz.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lz.correctionRegion G.lz.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).topCenter G.topCenter ∧
    HEq (transportEndpoint P U V S h G).correctionOwner G.correctionOwner := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- Every region is the actual owner fibre, up to the defining successor cast. -/
theorem rxData_coordinates (h : i.val % 2 = 0) :
    HEq (rxLx S depth i h).syndromeRegion (localX (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLx S depth i h).correctionRegion (localX (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLq S depth i h).syndromeRegion (localQ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLq S depth i h).correctionRegion (localQ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLz S depth i h).syndromeRegion (localZ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLz S depth i h).correctionRegion (localZ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxData S depth i h).topCenter (topCenter (state S i.val).presentation S) ∧
    HEq (correctionOwnerAt S depth i h)
      (fun p => (vertexEquiv (state S i.val).presentation).symm
        (rxCorrectionOwner (state S i.val).presentation S p)) := by
  exact transportEndpoint_regions _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)

/-- The graph is precisely the original Tanner graph through the tag equivalence. -/
theorem rxData_graph_edge (h : i.val % 2 = 0)
    (u v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z) :
    (rxData S depth i h).levelGraph.graph.edge u v =
      (tannerLevel (state S i.val).presentation).graph.edge
        (vertexEquiv (state S i.val).presentation u) (vertexEquiv (state S i.val).presentation v) := rfl

/-- The same radius-one bound in the original Tanner graph's vertex type. -/
theorem rxStepOutput_component_boundary_radius_actual (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (p : FamilyZ S depth i.succ)
    (hp : (rxStepOutput S depth i h sigma).componentCoboundaryAt j p ≠ 0) :
    DirectedGraph.distance (tannerLevel (state S i.val).presentation).graph
      (vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j))
      (vertexEquiv (state S i.val).presentation ((rxData S depth i h).topCenter p)) ≤ 1 := by
  apply (distance_le_one_iff _ _ _).mpr
  have hd := rxStepOutput_component_boundary_radius_one S depth i h sigma j p hp
  rcases (distance_le_one_iff _ _ _).mp hd with he | he
  · exact Or.inl (congrArg (vertexEquiv (state S i.val).presentation) he)
  · right
    rw [← rxData_graph_edge S depth i h]
    exact he


/-! ## Derived actual Q-cylinder coordinates for tail diagnostics -/

private abbrev EndpointQCoordinates {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) :=
  ∀ q : P.Q, QDoubleCylinderVertex P q S ≃ LocalRegionIndex (G.lq.correctionRegion q)

private noncomputable def transportQCoordinates
    (P U V : TannerSquarePresentation) (S : OddScale) (h : U = V)
    (G : EndpointData P V S) (E : EndpointQCoordinates G) :
    EndpointQCoordinates (transportEndpoint P U V S h G) := by
  cases h
  exact E

private def EndpointQKernel {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) (E : EndpointQCoordinates G) : Prop :=
  ∀ q (w : Word BDL26Field (LocalRegionIndex (G.lq.correctionRegion q))),
    wordLinearMapTranspose (G.cq q).boundary2 w = 0 →
    ∀ v, w (E q v) = w (E q (0, Sum.inl (Sum.inl ())))

private theorem actualEndpoint_qKernel (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointQKernel (actualEndpoint P A R S) (qCorrectionEquiv P S) := by
  intro q w hw v
  let raw : Word BDL26Field (QDoubleCylinderVertex P q S) :=
    fun t => w (qCorrectionEquiv P S q t)
  have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) raw = 0 := by
    funext e
    have he := congrFun hw (qSyndromeEquiv P S q e)
    change wordLinearMapTranspose (localCq P S q).boundary2 w
      (qSyndromeEquiv P S q e) = 0 at he
    exact (localCq_delta1_apply P S q w e).symm.trans he
  exact word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A.toTannerSquareAdmissible q S)
    raw hz v

private theorem transportQKernel (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (E : EndpointQCoordinates G)
    (hk : EndpointQKernel G E) :
    EndpointQKernel (transportEndpoint P U V S h G)
      (transportQCoordinates P U V S h G E) := by
  cases h
  exact hk

/-- Literal actual cylinder vertices, transported only by the defining RX successor. -/
noncomputable def rxQVertexEquiv (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) :
    QDoubleCylinderVertex (state S i.val).presentation q S ≃
      LocalRegionIndex ((rxLq S depth i h).correctionRegion q) :=
  transportQCoordinates _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (qCorrectionEquiv (state S i.val).presentation S) q

/-- Actual connectedness, including the admissible bridge between copies. -/
theorem rxQ_kernel_constant (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).correctionRegion q)))
    (hw : (rxContract S depth i h).rx_local_complexes.cqDelta1 q w = 0)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    w (rxQVertexEquiv S depth i h q v) =
      w (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))) := by
  have hk := transportQKernel _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (qCorrectionEquiv (state S i.val).presentation S)
    (actualEndpoint_qKernel (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  exact hk q w hw v

private def EndpointConstantMap1 {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ c : Word BDL26Field P.Q, G.map1 c =
    ∑ q, extendWordLinear (G.lq.correctionRegion q) (fun _ => c q)

private theorem actualEndpoint_constantMap1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointConstantMap1 (actualEndpoint P A R S) := by
  intro c
  change rxMap1Coord P S c = ∑ q, extendWordLinear ((localQ P S).correctionRegion q) (fun _ => c q)
  rw [map1_representative_decomposition P A.toTannerSquareAdmissible S]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  funext p
  exact qRepresentative_value P A.toTannerSquareAdmissible S q c p

private theorem transportConstantMap1 (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (hc : EndpointConstantMap1 G) :
    EndpointConstantMap1 (transportEndpoint P U V S h G) := by
  cases h
  exact hc

/-- The actual selected degree-one map is exactly the constant-Q representative. -/
theorem rxMap1_constant_Q (h : i.val % 2 = 0)
    (c : Word BDL26Field (state S i.val).presentation.Q) :
    ((indexedDecoderData S depth).rxMap i).map1 c =
      ∑ q, extendWordLinear ((rxLq S depth i h).correctionRegion q) (fun _ => c q) := by
  have hc := transportConstantMap1 _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_constantMap1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  change (indexedEdgeMap S depth i).map1 c = _
  rw [← (endpointAt_maps S depth i h).2.1]
  exact hc c


private def EndpointXBoundaryZero {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ x f z b, tannerCoboundary1 U (extendWordLinear (G.lx.correctionRegion x) f)
    (G.pairEquiv (z,b)).val = 0

private theorem actualEndpoint_xBoundaryZero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointXBoundaryZero (actualEndpoint P A R S) := by
  intro x f z b
  let G := actualEndpoint P A R S
  have hp : (G.pairEquiv (z,b)).val ∉ G.lx.syndromeRegion x := by
    change Sum.inr (z,b) ∉ (localX P S).syndromeRegion x
    intro hm
    have hh := (Finset.mem_filter.mp hm).2
    cases hh
  have he : extendWordLinear (G.lx.syndromeRegion x)
      (wordLinearMapTranspose (G.cx x).boundary2 f) (G.pairEquiv (z,b)).val = 0 := by
    exact dif_neg hp
  have hf : G.xFlow x f (G.pairEquiv (z,b)).val = 0 :=
    xFlow_at_z P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f) z b
  rw [G.xDecomposition]
  exact (congrArg₂ (· + ·) he hf).trans (zero_add 0)

private theorem transportXBoundaryZero (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (hz : EndpointXBoundaryZero G) :
    EndpointXBoundaryZero (transportEndpoint P U V S h G) := by
  cases h
  exact hz

/-- Actual X correction boundaries have no Z endpoint contribution. -/
theorem rxX_boundary_z_zero (h : i.val % 2 = 0)
    (x : (state S i.val).presentation.X)
    (f : Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x)))
    (z : (state S i.val).presentation.Z) (b : Fin 2) :
    (indexedFamily S depth).coboundary1 i.succ
      (extendWordLinear ((rxLx S depth i h).correctionRegion x) f)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val = 0 := by
  have hz := transportXBoundaryZero _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_xBoundaryZero (state S i.val).presentation
      (state S i.val).admissible (state S i.val).regular S)
  rw [indexedFamily_coboundary1]
  exact hz x f z b

private theorem transportBoundaryZ (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (e : Word BDL26Field V.Q)
    (he : ∀ z b, tannerCoboundary1 V e (G.pairEquiv (z,b)).val = 0) :
    ∀ z b, tannerCoboundary1 U
      (Eq.mpr (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e)
      ((transportEndpoint P U V S h G).pairEquiv (z,b)).val = 0 := by
  cases h
  exact he

/-- Transport an actual raw zero Z-boundary using the defining RX successor. -/
theorem rxTransport_boundary_z_zero (h : i.val % 2 = 0)
    (e : Word BDL26Field (RX1 (state S i.val).presentation S))
    (he : ∀ z b, rxCoboundary1 (state S i.val).presentation S e (Sum.inr (z,b)) = 0) :
    ∀ z b, (indexedFamily S depth).coboundary1 i.succ
      (Eq.mpr (congrArg (fun C : ConstructionState => Word BDL26Field C.presentation.Q)
        (stateSuccRX S depth i h)) e)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val = 0 := by
  intro z b
  rw [indexedFamily_coboundary1]
  exact transportBoundaryZ _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) e (by
      intro z b
      exact (congrFun (LinearMap.congr_fun
        (rxPresentation_coboundary1_eq (state S i.val).presentation
          (state S i.val).admissible (state S i.val).regular S) e)
        (Sum.inr (z,b))).trans (he z b)) z b


private def EndpointQBoundaryFlow {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ q f z b, tannerCoboundary1 U (extendWordLinear (G.lq.correctionRegion q) f)
    (G.pairEquiv (z,b)).val = G.qFlow q f (G.pairEquiv (z,b)).val

private theorem actualEndpoint_qBoundaryFlow (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointQBoundaryFlow (actualEndpoint P A R S) := by
  intro q f z b
  let G := actualEndpoint P A R S
  have hp : (G.pairEquiv (z,b)).val ∉ G.lq.syndromeRegion q := by
    change Sum.inr (z,b) ∉ (localQ P S).syndromeRegion q
    intro hm
    have hh := (Finset.mem_filter.mp hm).2
    cases hh
  have he : extendWordLinear (G.lq.syndromeRegion q)
      (wordLinearMapTranspose (G.cq q).boundary2 f) (G.pairEquiv (z,b)).val = 0 := by
    exact dif_neg hp
  rw [G.qDecomposition]
  exact (congrArg (fun t => t + G.qFlow q f (G.pairEquiv (z,b)).val) he).trans (zero_add _)

private theorem transportQBoundaryFlow (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (hz : EndpointQBoundaryFlow G) :
    EndpointQBoundaryFlow (transportEndpoint P U V S h G) := by
  cases h
  exact hz

/-- Actual Q boundaries at either Z endpoint are exactly their outgoing flow. -/
theorem rxQ_boundary_z_flow (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (f : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).correctionRegion q)))
    (z : (state S i.val).presentation.Z) (b : Fin 2) :
    (indexedFamily S depth).coboundary1 i.succ
      (extendWordLinear ((rxLq S depth i h).correctionRegion q) f)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val =
    (rxContract S depth i h).support_decomposition.cqFlow q f
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val := by
  have hz := transportQBoundaryFlow _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_qBoundaryFlow (state S i.val).presentation
      (state S i.val).admissible (state S i.val).regular S)
  rw [indexedFamily_coboundary1]
  exact hz q f z b

end QEC.Coding.BDL26RXDecoderAdapter


/-! ## Canonical RX output on one literal materialized edge -/
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators

def presentationAt (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rxReplacementPresentation P S)

abbrev PresentationX (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).X
abbrev PresentationQ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).Q
abbrev PresentationZ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).Z

def presentationFamily (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26CochainFamily 1
      (PresentationX P A R S) (PresentationQ P A R S) (PresentationZ P A R S) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (presentationAt P A R S i)

theorem presentationFamily_coboundary0 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A R S).coboundary0 i = tannerCoboundary0 (presentationAt P A R S i) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q

theorem presentationFamily_coboundary1 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A R S).coboundary1 i = tannerCoboundary1 (presentationAt P A R S i) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z

def presentationMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26CochainMap (presentationFamily P A R S) (0 : StepIndex 1) where
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S
  commutes_coboundary0 := by
    rw [presentationFamily_coboundary0,presentationFamily_coboundary0]
    exact by
      erw [rxPresentation_coboundary0_eq P A R S]
      exact rxMap_commutes_coboundary0 P A.toTannerSquareAdmissible S
  commutes_coboundary1 := by
    rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
    exact by
      erw [rxPresentation_coboundary1_eq P A R S]
      exact rxMap_commutes_coboundary1 P S

def presentationDecoderData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26DecoderData 1
      (PresentationX P A R S) (PresentationQ P A R S) (PresentationZ P A R S) where
  family := presentationFamily P A R S
  rxMap := fun i => Fin.cases (presentationMap P A R S) (fun j => Fin.elim0 j) i
  rzMap := fun i => Fin.cases (presentationMap P A R S) (fun j => Fin.elim0 j) i

@[simp] theorem presentationDecoderData_selectedMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (presentationDecoderData P A R S).selectedMap (0 : StepIndex 1) =
      presentationMap P A R S := rfl


private theorem presentationEndpoint_maps (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (actualEndpoint P A R S).map0 = (presentationMap P A R S).map0 ∧
    (actualEndpoint P A R S).map1 = (presentationMap P A R S).map1 ∧
    (actualEndpoint P A R S).map2 = (presentationMap P A R S).map2 :=
  ⟨rfl,rfl,rfl⟩

noncomputable def presentationLx (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lx
noncomputable def presentationLq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lq
noncomputable def presentationLz (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lz

private noncomputable def presentationLocalComplexes (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXLocalComplexData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) where
  cx := (actualEndpoint P A R S).cx
  cq := (actualEndpoint P A R S).cq
  cz := rxCz P

private noncomputable def presentationSupport (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXSupportDecomposition (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLocalComplexes P A R S) := by
  let G := actualEndpoint P A R S
  refine
    { cxFlow := G.xFlow
      cqFlow := G.qFlow
      cxLift0 := G.xLift
      cqLift0 := fun _ => 0
      cxDelta1_restriction := ?_
      cxDelta1_restriction_global := ?_
      cqDelta1_restriction := ?_
      cqDelta1_restriction_global := ?_
      cxDelta0_restriction := ?_
      cxDelta0_sum_decomposition := ?_
      cxDelta1_decomposition := ?_
      cqDelta1_decomposition := ?_
      cxFlow_outside_x_sector := ?_
      cqFlow_outside_q_sector := ?_
      cx_regions_pairwise_disjoint := G.xSyndromeDisjoint
      cq_regions_pairwise_disjoint := G.qSyndromeDisjoint }
  · intro x f
    have hr := G.xRestriction x (extendWordLinear (G.lx.correctionRegion x) f)
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x)
      (d (extendWordLinear (G.lx.correctionRegion x) f)))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cx x).boundary2)
          (region_restrict_extend (G.lx.correctionRegion x) f)))
  · intro x e
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x) (d e))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.xRestriction x e)
  · intro q f
    have hr := G.qRestriction q (extendWordLinear (G.lq.correctionRegion q) f)
      (fun x => region_restrict_extend_disjoint _ _ (G.xqCorrectionDisjoint x q).symm f)
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q)
      (d (extendWordLinear (G.lq.correctionRegion q) f)))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cq q).boundary2)
          (region_restrict_extend (G.lq.correctionRegion q) f)))
  · intro q e hx
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q) (d e))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.qRestriction q e hx)
  · intro x s
    exact (congrArg (fun d => restrictWordLinear (G.lx.correctionRegion x) (d (G.xLift x s)))
      (presentationFamily_coboundary0 P A R S (1 : LevelIndex 1))).trans
        (G.xLiftRestriction x s)
  · intro s x
    exact (congrArg (fun d => restrictWordLinear (G.lx.correctionRegion x)
      (d (∑ y, G.xLift y (s y))))
      (presentationFamily_coboundary0 P A R S (1 : LevelIndex 1))).trans (G.xLiftSum s x)
  · intro x f
    exact (congrArg (fun d => d (extendWordLinear (G.lx.correctionRegion x) f))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.xDecomposition x f)
  · intro q f
    exact (congrArg (fun d => d (extendWordLinear (G.lq.correctionRegion q) f))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.qDecomposition q f)
  · intro x f p hp
    exact G.xFlowZeroX x f p (G.xsRegions.symm ▸ hp)
  · intro q f p hp
    exact G.qFlowZeroQ q f p (G.qsRegions.symm ▸ hp)

/-- Actual F04/F06/F11/F12 contract, with no caller-supplied proof certificate. -/
noncomputable def presentationContract (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) where
  rx_local_complexes := presentationLocalComplexes P A R S
  rx_local_cohomology :=
    { cx_h1_ker_eq_range := (actualEndpoint P A R S).cxExact
      cq_h1_finrank := (actualEndpoint P A R S).cqFinrank }
  support_decomposition := presentationSupport P A R S
  local_boundary_weight_budgets :=
    { cx := (actualEndpoint P A R S).xBudget
      cq := (actualEndpoint P A R S).qBudget }

private noncomputable def presentationRepresentative (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : P.Q) :
    ((presentationContract P A R S).rx_local_complexes.cq q).middleCohomology →ₗ[BDL26Field]
      ((presentationContract P A R S).rx_local_complexes.cq q).middleCocycleCode.carrier :=
  (actualEndpoint P A R S).representative q

private theorem presentationRepresentative_section (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (q : P.Q) (v) :
    ((presentationContract P A R S).rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
      (presentationRepresentative P A R S q v) = v :=
  (actualEndpoint P A R S).representativeSection q v

private theorem presentationRepresentative_support (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (q : P.Q) (v)
    (p : LocalRegionIndex ((presentationLq P A R S).correctionRegion q))
    (hp : p.1 ∉ (actualEndpoint P A R S).qcs) :
    (presentationRepresentative P A R S q v).1 p = 0 :=
  (actualEndpoint P A R S).representativeSupport q v p hp

private noncomputable def presentationQuotientEquiv (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (∀ q, ((presentationContract P A R S).rx_local_complexes.cq q).middleCohomology) ≃ₗ[BDL26Field]
      (presentationDecoderData P A R S).family.Cochain1 (0 : LevelIndex 1) :=
  (actualEndpoint P A R S).quotientEquiv

/-- Actual indexed RX coarse-graining data in every even-lower-index step. -/
noncomputable def presentationData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) := by
  let G := actualEndpoint P A R S
  refine
    { induced :=
        { adjacencyMap := rxXQAdjacency P
          gXQ0 := actualGXQ0 P A.toTannerSquareAdmissible S
          gXQ0_eq_adjacency := actualGXQ0_eq_adjacency P A.toTannerSquareAdmissible S
          qzAdjacency := rxQZAdjacency P
          gQZ1 := actualGQZ1 P S
          gQZ1_eq_diagonal_comp := actualGQZ1_eq_diagonal P A.toTannerSquareAdmissible S
          zSector := G.zs
          zPairEquiv := G.pairEquiv
          map2_diagonal := ?_
          map2_auxiliary_zero := ?_ }
      contract := presentationContract P A R S
      xSector := G.xs
      qSector := G.qs
      zSector := G.zs
      zSector_eq_induced := rfl
      xSector_eq_regions := G.xsRegions
      qSector_eq_regions := G.qsRegions
      sectors_pairwise_disjoint := G.sectorsDisjoint
      sectors_cover := G.sectorsCover
      qCorrectionSector := G.qcs
      qCorrectionSector_eq_regions := G.qcsRegions
      correction_sectors_cover := G.correctionsCover
      correction_sectors_disjoint := G.correctionsDisjoint
      qRepresentativeSector := G.qcs
      qRepresentativeSector_subset_qCorrectionSector := Finset.Subset.refl _
      cqRepresentative := presentationRepresentative P A R S
      cqRepresentative_mkQ := presentationRepresentative_section P A R S
      cqRepresentative_supported := presentationRepresentative_support P A R S
      qCohomologyEquiv := presentationQuotientEquiv P A R S
      rxMap1_eq_cqRepresentative := ?_
      cqDelta0_sum_decomposition := ?_
      cqFlow_outside_xSector := G.qFlowZeroX
      levelGraph := rxLevel P
      levelGraph_kind_x := fun _ => rfl
      levelGraph_kind_q := fun _ => rfl
      levelGraph_kind_z := fun _ => rfl
      topCenter := G.topCenter
      coarseCenter := fun z => .inr (.inr z)
      coarseCenter_is_z := fun z => ⟨z,rfl⟩
      topCenter_coarse_pair := G.centerPair
      topCenter_x_iff := G.centerX
      topCenter_q_iff := G.centerQ
      topCenter_z_iff := G.centerZ
      zSector_eq_regions := G.zsRegions
      lz_regions_pairwise_disjoint := G.zSyndromeDisjoint
      cx_correction_regions_pairwise_disjoint := G.xCorrectionDisjoint
      cq_correction_regions_pairwise_disjoint := G.qCorrectionDisjoint
      cxFlow_radius_one := G.xRadius
      cqFlow_radius_one := G.qRadius
      distance_one_comp := distance_one_comp _ }
  · intro w z b
    change (presentationMap P A R S).map2 w (G.pairEquiv (z,b)).1 = w z
    rw [← (presentationEndpoint_maps P A R S).2.2]
    exact G.map2Diagonal w z b
  · intro w p hp
    change (presentationMap P A R S).map2 w p = 0
    rw [← (presentationEndpoint_maps P A R S).2.2]
    exact G.map2Auxiliary w p hp
  · intro w
    change (presentationMap P A R S).map1 w = _
    rw [← (presentationEndpoint_maps P A R S).2.1]
    exact G.map1Representative w
  · intro s
    change (presentationFamily P A R S).coboundary0 (1 : LevelIndex 1) (∑ q, (0 : _ →ₗ[BDL26Field] _) (s q)) =
      ∑ q, extendWordLinear (G.lq.correctionRegion q) (wordLinearMapTranspose (G.cq q).boundary1 (s q))
    simp only [LinearMap.zero_apply, Finset.sum_const_zero, map_zero, G.qDelta0Zero]
    rfl


open RXCoarseGrainingData

/-- The original canonical RX words evaluated once on the literal local edge. -/
noncomputable def presentationOutput
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    AssemblyStepOutput (presentationDecoderData P A R S) (0 : StepIndex 1) := by
  let G := presentationData P A R S
  have hs := rx_coarse_graining_selected G rfl sigma
  have hrange : rxCoarseWord G sigma.val ∈
      LinearMap.range ((presentationFamily P A R S).coboundary1 (0 : LevelIndex 1)) := by
    obtain ⟨coarse,correction,hword,hcorrection,hrelation,hrest⟩ := hs
    rw [← hword]
    exact coarse.property
  let actualCoarse : (presentationFamily P A R S).Syndrome (0 : LevelIndex 1) :=
    ⟨rxCoarseWord G sigma.val,hrange⟩
  let actualCorrection := rxCorrectionTotal G sigma.val
  let pieces := (Finset.univ : Finset (RXVertex P.X P.Q P.Z)).toList.map
    (fun v => (rxLocalComponents G).component v sigma.val)
  apply AssemblyStepOutput.ofComponents sigma actualCoarse actualCorrection pieces
  · obtain ⟨coarse,correction,hword,hcorrection,hrelation,hrest⟩ := hs
    have hc : actualCoarse = coarse := Subtype.ext hword.symm
    simpa only [hc,actualCorrection,← hcorrection] using hrelation
  · dsimp [actualCorrection]
    calc
      rxCorrectionTotal G sigma.val =
          (∑ x, cxComponentTotal G sigma.val x) + ∑ q, cqComponentTotal G sigma.val q :=
        rx_total_eq_components G sigma.val
      _ = pieces.sum := by
        simp [pieces,rxLocalComponents,LocalCorrectionComponents.totalCorrection,
          Fintype.sum_sum_type]

@[simp] theorem presentationOutput_correction
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A R S sigma).correction =
      rxCorrectionTotal (presentationData P A R S) sigma.val := rfl

@[simp] theorem presentationOutput_coarse
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A R S sigma).coarse.val =
      rxCoarseWord (presentationData P A R S) sigma.val := rfl

@[simp] theorem presentationOutput_components
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A R S sigma).localComponents =
      (Finset.univ : Finset (RXVertex P.X P.Q P.Z)).toList.map
        (fun v => (rxLocalComponents (presentationData P A R S)).component v sigma.val) := rfl

end QEC.Coding.BDL26RXDecoderAdapter
end

namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
/-- Zero coarse syndrome follows from the actual factor-two bound. The chosen
zero-run correction is retained and need not itself be zero. -/
theorem presentationOutput_zero_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1))
    (hs : sigma.val = 0) : (presentationOutput P A R S sigma).coarse.val = 0 := by
  obtain ⟨coarse,correction,hword,hcorrection,hrelation,hw,hrest⟩ :=
    rx_coarse_graining_selected (presentationData P A R S) rfl sigma
  rw [presentationOutput_coarse,← hword]
  apply (HammingWeight_eq_zero_iff _).mp
  rw [hs,HammingWeight_zero] at hw
  omega
end QEC.Coding.BDL26RXDecoderAdapter

/-! ## Derived X-cylinder geometry for the one-X transport

These constructions only expose the actual endpoint already used above.
In particular the upper degree-zero chart is transported by the defining
successor equality; no coordinate equivalence is an input to the API.
-/
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators

private abbrev EndpointXCoordinates {P U : TannerSquarePresentation} {S : OddScale}
    (_G : EndpointData P U S) :=
  (Σ x : P.X, DoubleCylinderVertex P x S) ≃ U.X

private def EndpointXLiftGeometry {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) (E : EndpointXCoordinates G) : Prop :=
  (∀ x w v, G.xLift x w (E ⟨x,v⟩) = w v) ∧
  (∀ x y, y ≠ x → ∀ w v, G.xLift x w (E ⟨y,v⟩) = 0) ∧
  (∀ x y, y ≠ x → ∀ w, restrictWordLinear (G.lx.correctionRegion y)
    (tannerCoboundary0 U (G.xLift x w)) = 0) ∧
  (∀ x q, P.xq x q ≠ true → ∀ w,
    restrictWordLinear (G.lq.correctionRegion q)
      (tannerCoboundary0 U (G.xLift x w)) = 0)

private theorem raw_xLift_q_zero (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q ≠ true)
    (w : Word BDL26Field (DoubleCylinderVertex P x S))
    (v : QDoubleCylinderVertex P q S) :
    rxCoboundary0 P S (xLift P S x w) (Sum.inr ⟨q,v⟩) = 0 := by
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro u _
  by_cases hy : y = x
  · subst y
    simp [rxBoundary1Matrix, qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence, hxq]
  · rw [xLift_other P S x y hy w u, zero_mul]

private theorem actualEndpoint_xLiftGeometry (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointXLiftGeometry (actualEndpoint P A R S) (Equiv.refl _) := by
  refine ⟨xLift_same P S, xLift_other P S, ?_, ?_⟩
  · intro x y hy w
    funext p
    obtain ⟨e,rfl⟩ := (xCorrectionEquiv P S y).surjective p
    rw [rxPresentation_coboundary0_eq P A R S]
    change rxCoboundary0 P S (xLift P S x w) (Sum.inl ⟨y,e⟩) = 0
    rw [raw_delta0_x]
    have hz : (fun v => xLift P S x w ⟨y,v⟩) = 0 := by
      funext v
      exact xLift_other P S x y hy w v
    rw [hz, map_zero]
    rfl
  · intro x q hxq w
    funext p
    obtain ⟨v,rfl⟩ := (qCorrectionEquiv P S q).surjective p
    rw [rxPresentation_coboundary0_eq P A R S]
    exact raw_xLift_q_zero P S x q hxq w v

private noncomputable def transportXCoordinates
    (P U V : TannerSquarePresentation) (S : OddScale) (h : U = V)
    (G : EndpointData P V S) (E : EndpointXCoordinates G) :
    EndpointXCoordinates (transportEndpoint P U V S h G) := by
  cases h
  exact E

private theorem transportXLiftGeometry
    (P U V : TannerSquarePresentation) (S : OddScale) (h : U = V)
    (G : EndpointData P V S) (E : EndpointXCoordinates G)
    (hg : EndpointXLiftGeometry G E) :
    EndpointXLiftGeometry (transportEndpoint P U V S h G)
      (transportXCoordinates P U V S h G E) := by
  cases h
  exact hg

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

/-- All actual upper degree-zero coordinates, retaining the cylinder owner. -/
def rxDegreeZeroEquiv :
    (Σ x : (state S i.val).presentation.X,
      DoubleCylinderVertex (state S i.val).presentation x S) ≃ FamilyX S depth i.succ :=
  transportXCoordinates _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) (Equiv.refl _)

private theorem indexed_xLiftGeometry :
    EndpointXLiftGeometry (endpointAt S depth i h) (rxDegreeZeroEquiv S depth i h) :=
  transportXLiftGeometry _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) (Equiv.refl _)
    (actualEndpoint_xLiftGeometry (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)

theorem rxXLift_same (x : (state S i.val).presentation.X)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S))
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    (rxContract S depth i h).support_decomposition.cxLift0 x w
      (rxDegreeZeroEquiv S depth i h ⟨x,v⟩) = w v :=
  (indexed_xLiftGeometry S depth i h).1 x w v

theorem rxXLift_other (x y : (state S i.val).presentation.X) (hy : y ≠ x)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S))
    (v : DoubleCylinderVertex (state S i.val).presentation y S) :
    (rxContract S depth i h).support_decomposition.cxLift0 x w
      (rxDegreeZeroEquiv S depth i h ⟨y,v⟩) = 0 :=
  (indexed_xLiftGeometry S depth i h).2.1 x y hy w v

theorem rxXLift_boundary_other_x (x y : (state S i.val).presentation.X) (hy : y ≠ x)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y)
      ((indexedFamily S depth).coboundary0 i.succ
        ((rxContract S depth i h).support_decomposition.cxLift0 x w)) = 0 := by
  rw [indexedFamily_coboundary0]
  exact (indexed_xLiftGeometry S depth i h).2.2.1 x y hy w

theorem rxXLift_boundary_nonincident_q (x : (state S i.val).presentation.X)
    (q : (state S i.val).presentation.Q) (hxq : (state S i.val).presentation.xq x q ≠ true)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    restrictWordLinear ((rxLq S depth i h).correctionRegion q)
      ((indexedFamily S depth).coboundary0 i.succ
        ((rxContract S depth i h).support_decomposition.cxLift0 x w)) = 0 := by
  rw [indexedFamily_coboundary0]
  exact (indexed_xLiftGeometry S depth i h).2.2.2 x q hxq w

private def EndpointXGradientKernel {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ x (w : Word BDL26Field (DoubleCylinderVertex P x S)),
    wordLinearMapTranspose (G.cx x).boundary1 w = 0 ↔
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S) w = 0

private theorem actualEndpoint_xGradientKernel (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointXGradientKernel (actualEndpoint P A R S) := by
  intro x w
  constructor
  · intro hz
    funext e
    exact (localCx_delta0_apply P S x w e).symm.trans
      (congrFun hz (xCorrectionEquiv P S x e))
  · intro hz
    funext p
    obtain ⟨e,rfl⟩ := (xCorrectionEquiv P S x).surjective p
    exact (localCx_delta0_apply P S x w e).trans (congrFun hz e)

private theorem transportXGradientKernel
    (P U V : TannerSquarePresentation) (S : OddScale) (hh : U = V)
    (G : EndpointData P V S) (hk : EndpointXGradientKernel G) :
    EndpointXGradientKernel (transportEndpoint P U V S hh G) := by
  cases hh
  exact hk

/-- Actual local gradients have precisely the literal cylinder gradient kernel. -/
theorem rxCxDelta0_eq_zero_iff_raw (x : (state S i.val).presentation.X)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    (rxContract S depth i h).rx_local_complexes.cxDelta0 x w = 0 ↔
      wordLinearMapTranspose (doubleCylinderBoundary1 (state S i.val).presentation x S) w = 0 :=
  transportXGradientKernel _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_xGradientKernel (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) x w

end QEC.Coding.BDL26RXDecoderAdapter

/-! ## Actual physical-coordinate transport identities

These equalities expose the defining RX successor transport.  The generic
proofs eliminate equality between presentations before any dependent carrier
is specialized; their actual consumers derive that equality from parity.
-/
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder

private theorem transportXCoordinates_vertex
    (P U V : TannerSquarePresentation) (S : OddScale) (hp : U = V)
    (hv : Vertex U = Vertex V) (G : EndpointData P V S)
    (E : EndpointXCoordinates G)
    (r : Σ x : P.X, DoubleCylinderVertex P x S) :
    cast hv (Vertex.x ((transportXCoordinates P U V S hp G E) r)) =
      Vertex.x (E r) := by
  cases hp
  rfl

private theorem transportXCoordinates_xq
    (P U V : TannerSquarePresentation) (S : OddScale) (hp : U = V)
    (hq : V.Q = U.Q) (G : EndpointData P V S)
    (E : EndpointXCoordinates G)
    (r : Σ x : P.X, DoubleCylinderVertex P x S) (q : V.Q) :
    U.xq ((transportXCoordinates P U V S hp G E) r) ((Equiv.cast hq) q) =
      V.xq (E r) q := by
  cases hp
  rfl

private theorem cast_vertex_q_cast
    (U V : TannerSquarePresentation) (hp : U = V)
    (hv : Vertex U = Vertex V) (hq : V.Q = U.Q) (q : V.Q) :
    cast hv (Vertex.q ((Equiv.cast hq) q)) = Vertex.q q := by
  cases hp
  rfl

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

/-- The complete physical Q chart comes from the actual parity successor. -/
def rxPhysicalQEquiv :
    RX1 (state S i.val).presentation S ≃ FamilyQ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Q)
    (stateSuccRX S depth i h)).symm

/-- The actual upper X chart computes the existing partial graph parent. -/
theorem rxDegreeZero_parent (x : (state S i.val).presentation.X)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.x (rxDegreeZeroEquiv S depth i h ⟨x,v⟩)) =
      some (Vertex.x x) := by
  simp only [parent,nextParent,dif_pos h,nextRXVertex,rxDegreeZeroEquiv]
  erw [transportXCoordinates_vertex]
  rfl

/-- Physical X-Q incidence is the literal materialized incidence on both charts. -/
theorem rxPhysical_incidence (r : RX0 (state S i.val).presentation S)
    (p : RX1 (state S i.val).presentation S) :
    (state S (i.val+1)).presentation.xq (rxDegreeZeroEquiv S depth i h r)
      (rxPhysicalQEquiv S depth i h p) = rxXQIncidence (state S i.val).presentation S r p := by
  unfold rxPhysicalQEquiv rxDegreeZeroEquiv
  erw [transportXCoordinates_xq]
  rfl

/-- Actual local-edge physical coordinates retain the literal absent parent. -/
theorem rxPhysical_localEdge_parent_none (x : (state S i.val).presentation.X)
    (e : DoubleCylinderEdge (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.q (rxPhysicalQEquiv S depth i h (Sum.inl ⟨x,e⟩))) =
      none := by
  simp only [parent,nextParent,dif_pos h,nextRXVertex,rxPhysicalQEquiv]
  erw [cast_vertex_q_cast _ _
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))]
  rfl

end QEC.Coding.BDL26RXDecoderAdapter


/-! ## Actual Q-cylinder coordinate value transport

The complete endpoint/region family is transported before taking its physical
value. This internal API supports exhaustive physical-coordinate traces.
-/
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

private theorem transportQCoordinates_val
    (P U V : TannerSquarePresentation) (S : OddScale) (hp : U = V)
    (hq : V.Q = U.Q) (G : EndpointData P V S) (E : EndpointQCoordinates G)
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    ((transportQCoordinates P U V S hp G E q) v).val =
      (Equiv.cast hq) (E q v).val := by
  cases hp
  rfl

/-- The actual Q-cylinder coordinate has its complete defining physical chart value. -/
theorem rxQVertexEquiv_val (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : (state S i.val).presentation.Q)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    (rxQVertexEquiv S depth i h q v).val =
      rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) := by
  calc
    (rxQVertexEquiv S depth i h q v).val =
        rxPhysicalQEquiv S depth i h
          (qCorrectionEquiv (state S i.val).presentation S q v).val :=
      transportQCoordinates_val (state S i.val).presentation
        (state S (i.val+1)).presentation
        (rxReplacementPresentation (state S i.val).presentation S) S
        (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
        (congrArg (fun C : ConstructionState => C.presentation.Q)
          (stateSuccRX S depth i h)).symm
        (actualEndpoint (state S i.val).presentation (state S i.val).admissible
          (state S i.val).regular S)
        (qCorrectionEquiv (state S i.val).presentation S) q v
    _ = rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) :=
      congrArg (rxPhysicalQEquiv S depth i h)
        (qCorrectionEquiv_val (state S i.val).presentation S q v)

end QEC.Coding.BDL26RXDecoderAdapter
end
