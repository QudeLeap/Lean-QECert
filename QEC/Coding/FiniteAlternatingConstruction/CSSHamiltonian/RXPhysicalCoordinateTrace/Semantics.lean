import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXPhysicalCoordinateTrace
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LocalSearchFailureReduction

/-!
# Same-history semantics of the geometric coordinate trace

The total depth, initial localized record and BOTH original histories are fixed
throughout induction. Safe leaves prove local C2 preimages or an actual zero
snapshot; residual leaves retain the actual original singleton snapshot.
No trace constructor stores any of these semantic properties.
-/
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators

theorem rx_vertex_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (he : (i.val+2)%2=0)
    (w : LocalizedWord S N sigma tau i.succ) (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (state S (i.val+2)).presentation q S)
    (hw : hammingSupport w.word ⊆
      {BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) he q v}) :
    (step S N sigma tau i w).potential=0 ∧
      hammingSupport (step S N sigma tau i w).lower.word ⊆ {q} := by
  have hh : (Edge N i).val%2=0 := by
    simpa only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep_val] using he
  have hs : hammingSupport (first S N sigma i+second S N sigma tau i w) ⊆
      (BDL26RXDecoderAdapter.rxLq S (N+2) (Edge N i) hh).correctionRegion q := by
    rw [representatives_difference]
    intro r hr
    have heq := Finset.mem_singleton.mp (hw hr)
    subst r
    exact (BDL26RXDecoderAdapter.rxQVertexEquiv S (N+2) (Edge N i) hh q v).property
  have hz := BDL26FirstZeroQVertexTower.rx_computed_parent S (N+2) (Edge N i) hh
    q _ _ hs w.center
  rw [step_rx S N sigma tau i hh w]
  constructor
  · exact hz.1
  · change hammingSupport (BDL26RXPhysicalStarTransport.L S (N+2) (Edge N i) hh
      w.center _ _) ⊆ {q}
    rw [hz.2]
    exact BDL26RXQBlockTransport.lower_supported S (N+2) (Edge N i) hh q _ _

theorem rz_vertex_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (ho : ¬(i.val+2)%2=0)
    (w : LocalizedWord S N sigma tau i.succ) (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (transposePresentation (state S (i.val+2)).presentation) q S)
    (hw : hammingSupport w.word ⊆
      {BDL26FirstZeroQVertexTower.rzVertex S (i.val+2) ho q v}) :
    hammingSupport (step S N sigma tau i w).lower.word ⊆ {q} := by
  have hh : ¬(Edge N i).val%2=0 := by
    simpa only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep_val] using ho
  obtain ⟨c,hc⟩ := BDL26RXQEdgePairTransport.scalar_singleton w.word _ hw
  rcases BDL26RXQEdgePairTransport.bit_cases c with rfl | rfl
  · have hz : w.word=0 := hc.trans (BDL26RXQEdgePairTransport.scalar_zero _)
    rw [BDL26RXQEdgePairTransport.step_zero S N sigma tau i w hz]
    simp [hammingSupport]
  · have hb : w.word=canonicalBasisWord (F:=F)
        (BDL26FirstZeroQVertexTower.rzVertex S (i.val+2) ho q v) :=
      hc.trans (BDL26RXQEdgePairTransport.scalar_one _)
    rw [step_rz S N sigma tau i hh w]
    change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (N+2) (Edge N i) hh
      (first S N sigma i) (first S N sigma i+w.word)) ⊆ {q}
    have hb' : w.word=(canonicalBasisWord
        (BDL26RZPhysicalStarTransport.physicalQ S (N+2) (Edge N i) hh q v) :
        BDL26RZErrorPullback.Upper S (N+2) (Edge N i)) := hb
    rw [hb']
    have hl := BDL26RZPhysicalStarTransport.lower_physicalQ_basis S (N+2) (Edge N i) hh
      (first S N sigma i) q v
    rw [hl]
    exact BDL26RXQEdgePairTransport.basis_supported q

/-- These are propositions ABOUT a constructed path, never fields of the trace. -/
def LeafMeaning (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) : Leaf S → Prop
  | .c2 r => hammingSupport (path S N sigma tau top 0).word ⊆ {r}
  | .face a => hammingSupport (path S N sigma tau top 0).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)
  | .killed b => ∃ hb : b≤N,
      (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word=0
  | @Leaf.primitive _ b p => ∃ hb : b≤N,
      hammingSupport (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word ⊆ {p.physical}

/-- Geometry induction preserves one total N, the same top, sigma and tau. -/
theorem trace_semantics {S : OddScale} {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
    (t : Trace S b q leaf) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (hb : b≤N)
    (hw : hammingSupport (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word ⊆ {q}) :
    LeafMeaning S N sigma tau top leaf := by
  induction t generalizing N with
  | c2 r => exact hw
  | face a =>
      let i : StepIndex N := ⟨0,by omega⟩
      have hs := BDL26RXFaceEdgeTower.seed_step_supported S N sigma tau hb a
        (path S N sigma tau top i.succ) hw
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ _
      rw [path_step]
      exact hs
  | rzEdge k ho z e =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hz := BDL26RZLocalEdgeTower.seed_step_zero S N sigma tau i ho
        (path S N sigma tau top i.succ) z e hw
      refine ⟨by omega,?_⟩
      change (path S N sigma tau top i.castSucc).word=0
      rw [path_step]
      exact hz
  | higherFace j a =>
      let hN : 2*j+3≤N := hb
      have hz := BDL26HigherRXFaceTower.seed_two_step_zero S N sigma tau j hN a
        (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ) hw
      have hpair : (BDL26RXQEdgePairTransport.pairResult S N sigma tau j hN
          (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ)).lower.word=0 := by
        rw [BDL26RXQEdgePairTransport.pair_original_steps]
        exact hz
      rw [BDL26RXQEdgePairTransport.pair_original_path] at hpair
      exact ⟨by omega,hpair⟩
  | primitive p => exact ⟨hb,hw⟩
  | @rx k r leaf t he v ih =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hs := (rx_vertex_supported S N sigma tau i he
        (path S N sigma tau top i.succ) r v hw).2
      apply ih N sigma tau top (by omega)
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ {r}
      rw [path_step]
      exact hs
  | @rz k r leaf t ho v ih =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hs := rz_vertex_supported S N sigma tau i ho
        (path S N sigma tau top i.succ) r v hw
      apply ih N sigma tau top (by omega)
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ {r}
      rw [path_step]
      exact hs
  | qEdgePair j a t ih =>
      let hN : 2*j+3≤N := hb
      have hs := BDL26RXQEdgePairTransport.pair_supported S N sigma tau j hN a
        (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ) hw
      rw [BDL26RXQEdgePairTransport.pair_original_path] at hs
      exact ih N sigma tau top (by omega) hs

/-- The actual flip initializes the trace semantics internally. -/
theorem parser_semantics (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) :
    LeafMeaning S N (input S N u) (perturbTop S N (input S N u) (flip S N q))
      (BDL26BoundaryTailInvariance.physicalTop S N u q) (parse S N q) := by
  apply trace_semantics (parsedTrace S N q) N _ _ _ (Nat.le_refl _)
  rw [path_top]
  change hammingSupport (flip S N q) ⊆ {q}
  rw [flip_eq_basis]
  exact BDL26RXQEdgePairTransport.basis_supported q

/-- Any actual C2 singleton has an internally derived owner-local preimage. -/
theorem c2_singleton_local (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (r : Physical S 2)
    (hh : hammingSupport (descent S N u q).word ⊆ {r}) :
    levelTwoLocalError S (descent S N u q).word := by
  obtain ⟨c,hc⟩ := BDL26RXQEdgePairTransport.scalar_singleton (descent S N u q).word r hh
  have hraw : (descent S N u q).word=c • (canonicalBasisWord (F:=F) r :
      BDL26LevelTwoLocalBranchEndpoint.Error S) := hc
  rcases BDL26RXQEdgePairTransport.bit_cases c with rfl | rfl
  · have hz : (descent S N u q).word=0 := hraw.trans (BDL26RXQEdgePairTransport.scalar_zero _)
    rw [hz]
    apply (levelTwoLocalError_iff_owner S _).mpr
    refine ⟨BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S r,?_⟩
    intro t ht
    exact False.elim (ht rfl)
  · have hb : (descent S N u q).word=BDL26FirstZeroEmptySuffix.physicalWord S r := by
      exact (hraw.trans (BDL26RXQEdgePairTransport.scalar_one _)).trans
        (flip_eq_basis S 0 r).symm
    rw [hb]
    exact BDL26FirstZeroEmptySuffix.physical_flip_local S r

private theorem star_operations_heq {P Q : TannerSquarePresentation} (hp : P=Q) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar P)
      (BDL26RXPhysicalStarTransport.physicalXStar Q) ∧
    HEq (fun w : Word F P.Q => hammingSupport w) (fun w : Word F Q.Q => hammingSupport w) := by
  cases hp
  exact ⟨HEq.rfl,HEq.rfl⟩

theorem c2_face_local (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : BDL26RXFaceEdgeTower.Seed S)
    (hh : hammingSupport (descent S N u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)) :
    levelTwoLocalError S (descent S N u q).word := by
  have hops := star_operations_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S))
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (RawTwo S).X → Finset (RawTwo S).Q)=
      BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) := eq_of_heq hops.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      BDL26LevelTwoLocalBranchEndpoint.Error S → Finset (RawTwo S).Q)=
      (fun w : BDL26LevelTwoLocalBranchEndpoint.Error S => hammingSupport w) := eq_of_heq hops.2
  apply BDL26FirstZeroFaceEndpoint.face_local S a.1 a.2.1 (descent S N u q).word
  intro r hr
  have hs := congrArg (fun f : BDL26LevelTwoLocalBranchEndpoint.Error S → Finset (RawTwo S).Q =>
    f (descent S N u q).word) hsupport
  have hx := congrArg (fun f : (RawTwo S).X → Finset (RawTwo S).Q =>
    f (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)) hstar
  exact Eq.mp (congrArg (fun a : Finset (RawTwo S).Q => r∈a) hx)
    (hh (Eq.mpr (congrArg (fun a : Finset (RawTwo S).Q => r∈a) hs) hr))

end QEC.Coding.BDL26RXPhysicalCoordinateTrace
