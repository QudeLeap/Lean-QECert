import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.HigherRXFaceTower
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RZLocalEdgeTower

/-!
# Original RX-edge / RZ-Q-edge singleton transport

Project-derived internal/API refinement of BDL26 paper.tex3398-3418,
3445-3480, SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b.
All steps belong to one original total depth and the same two histories.
The odd lower level is at least three; C3 Q-edge seeds remain residual.
Both scalar values and the complete adjacent potential are retained.
-/
noncomputable section
namespace QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators

theorem scalar_singleton {I : Type} [Fintype I] [DecidableEq I]
    (w : Word F I) (q : I) (hw : hammingSupport w ⊆ {q}) :
    ∃ c : F, w=c • canonicalBasisWord q := by
  refine ⟨w q,?_⟩
  funext r
  by_cases hr : r=q
  · subst r
    simp [canonicalBasisWord]
  · have hz : w r=0 := by
      by_contra hn
      exact hr (Finset.mem_singleton.mp
        (hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)))
    simp [canonicalBasisWord,hr,hz]

theorem bit_cases (c : F) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem scalar_zero {I : Type} (w : Word F I) : (0 : F) • w=0 := by
  funext r
  exact zero_mul _

theorem scalar_one {I : Type} (w : Word F I) : (1 : F) • w=w := by
  funext r
  exact one_mul _

theorem basis_supported {I : Type} [Fintype I] [DecidableEq I] (q : I) :
    hammingSupport (canonicalBasisWord (F:=F) q) ⊆ {q} := by
  intro r hr
  by_contra hn
  have hne : r≠q := by simpa only [Finset.mem_singleton] using hn
  exact (Finset.mem_filter.mp hr).2 (by simp [canonicalBasisWord,hne])

/-- Zero original differences are propagated without reading the stored centre. -/
theorem step_zero (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (w : LocalizedWord S N sigma tau i.succ) (hw : w.word=0) :
    (step S N sigma tau i w).lower.word=0 := by
  by_cases he : (Edge N i).val%2=0
  · have hs : second S N sigma tau i w=first S N sigma i := by
      dsimp only [second]
      rw [hw,add_zero]
    rw [step_rx S N sigma tau i he w]
    change BDL26RXPhysicalStarTransport.L S (N+2) (Edge N i) he w.center
      (first S N sigma i) (second S N sigma tau i w)=0
    rw [hs]
    exact BDL26RXPhysicalStarTransport.lower_self S (N+2) (Edge N i) he w.center _
  · rw [step_rz S N sigma tau i he w]
    change BDL26RZFiniteBlockTransport.lowerError S (N+2) (Edge N i) he
      (first S N sigma i) (second S N sigma tau i w)=0
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,
      representatives_difference,hw,map_zero,map_zero]

/-- Equality elimination moves the entire localized record and its support operation. -/
theorem localized_support_cast {S : OddScale} {N : Nat} {sigma tau : TopInput S N}
    {a b : LevelIndex N} (hab : a=b) (w : LocalizedWord S N sigma tau a) :
    HEq (hammingSupport (cast (congrArg (LocalizedWord S N sigma tau) hab) w).word)
      (hammingSupport w.word) := by
  cases hab
  rfl

theorem localized_cast_zero {S : OddScale} {N : Nat} {sigma tau : TopInput S N}
    {a b : LevelIndex N} (hab : a=b) (w : LocalizedWord S N sigma tau a)
    (hw : w.word=0) : (cast (congrArg (LocalizedWord S N sigma tau) hab) w).word=0 := by
  cases hab
  exact hw

/-- Every odd physical lower level above the stopping boundary is included. -/
theorem odd_ge_three (m : Nat) (hm : 3 ≤ m) (ho : ¬m%2=0) :
    ∃ j : Nat, m=2*j+3 := by
  refine ⟨(m-3)/2,?_⟩
  omega

def qEdgeOwner (S : OddScale) (j : Nat) (q : Physical S (2*j+3))
    (e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S) :
    (state S (2*j+4)).presentation.X :=
  BDL26RZPhysicalXStarTransport.upperXChart S (2*j+4) ⟨2*j+3,by omega⟩
    (by change ¬(2*j+3)%2=0; omega)
    (.inl (.inr ⟨q,e⟩))

abbrev Seed (S : OddScale) (j : Nat) :=
  Σ q : Physical S (2*j+3),
    Σ e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S,
      DoubleCylinderEdge (state S (2*j+4)).presentation (qEdgeOwner S j q e) S

def seedPhysical (S : OddScale) (j : Nat) (a : Seed S j) : Physical S (2*j+5) :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S (2*j+5) ⟨2*j+4,by omega⟩
    (by change (2*j+4)%2=0; omega)
    (.inl ⟨qEdgeOwner S j a.1 a.2.1,a.2.2⟩)

abbrev rxIndex := BDL26HigherRXFaceTower.rxIndex
abbrev rzIndex := BDL26HigherRXFaceTower.rzIndex

theorem index_pair (N j : Nat) (hN : 2*j+3≤N) :
    (rxIndex N j hN).castSucc=(rzIndex N j hN).succ :=
  (BDL26HigherRXFaceTower.seed_indices N j hN).2.2.symm

theorem rx_even (N j : Nat) (hN : 2*j+3≤N) : (Edge N (rxIndex N j hN)).val%2=0 := by
  exact BDL26HigherRXFaceTower.rx_index_even N j hN

theorem rz_odd (N j : Nat) (hN : 2*j+3≤N) : ¬(Edge N (rzIndex N j hN)).val%2=0 := by
  exact BDL26HigherRXFaceTower.rz_index_odd N j hN

theorem physical_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3≤N) (a : Seed S j) :
    seedPhysical S j a=BDL26RXDecoderAdapter.rxPhysicalQEquiv S (N+2)
      (Edge N (rxIndex N j hN)) (rx_even N j hN)
      (.inl ⟨qEdgeOwner S j a.1 a.2.1,a.2.2⟩) := by
  unfold seedPhysical BDL26RXDecoderAdapter.rxPhysicalQEquiv
  dsimp only [rxIndex,BDL26HigherRXFaceTower.rxIndex,
    BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep] <;> rfl

theorem owner_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3≤N)
    (q : Physical S (2*j+3))
    (e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S) :
    qEdgeOwner S j q e=BDL26RZPhysicalXStarTransport.upperXChart S (N+2)
      (Edge N (rzIndex N j hN)) (rz_odd N j hN) (.inl (.inr ⟨q,e⟩)) := by
  unfold qEdgeOwner BDL26RZPhysicalXStarTransport.upperXChart BDL26RZFiniteBlockTransport.coord0
  dsimp only [rzIndex,BDL26HigherRXFaceTower.rzIndex,
    BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep] <;> rfl

def middle (S : OddScale) (N : Nat) (sigma tau : TopInput S N) (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :
    LocalizedWord S N sigma tau (rzIndex N j hN).succ :=
  cast (congrArg (LocalizedWord S N sigma tau) (index_pair N j hN))
    (step S N sigma tau (rxIndex N j hN) w).lower

def pairResult (S : OddScale) (N : Nat) (sigma tau : TopInput S N) (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :=
  step S N sigma tau (rzIndex N j hN) (middle S N sigma tau j hN w)

/-- Incidence computes the original RX parent in the nonzero scalar branch. -/
theorem computed_parent (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    BDL26RXPhysicalStarTransport.parentX S (N+2) (Edge N (rxIndex N j hN))
      (rx_even N j hN) w.center=qEdgeOwner S j a.1 a.2.1 := by
  have hm : seedPhysical S j a ∈ hammingSupport w.word := by
    rw [hw]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hself : canonicalBasisWord (F:=F) (seedPhysical S j a)
        (seedPhysical S j a)=(1:F) := by
      simp [canonicalBasisWord,Pi.single_apply]
    exact fun hz => one_ne_zero (hself.symm.trans hz)
  have hi := w.supported hm
  change seedPhysical S j a ∈ BDL26RXPhysicalStarTransport.physicalXStar
    (state S (2*j+5)).presentation w.center at hi
  rw [physical_ambient S N j hN a] at hi
  exact BDL26HigherRXFaceTower.rx_local_edge_parent S (N+2)
    (Edge N (rxIndex N j hN)) (rx_even N j hN) w.center
      (qEdgeOwner S j a.1 a.2.1) a.2.2 hi

/-- The complete intermediate word lies in the literal actual Q-edge star. -/
theorem intermediate_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    hammingSupport (middle S N sigma tau j hN w).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (qEdgeOwner S j a.1 a.2.1) := by
  have hp := computed_parent S N sigma tau j hN a w hw
  have hs0 := (step S N sigma tau (rxIndex N j hN) w).lower.supported
  rw [step_rx S N sigma tau (rxIndex N j hN) (rx_even N j hN) w] at hs0
  change hammingSupport (BDL26RXPhysicalStarTransport.L S (N+2)
    (Edge N (rxIndex N j hN)) (rx_even N j hN) w.center _ _) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (BDL26RXPhysicalStarTransport.parentX S (N+2)
          (Edge N (rxIndex N j hN)) (rx_even N j hN) w.center) at hs0
  rw [hp] at hs0
  have hs : hammingSupport (step S N sigma tau (rxIndex N j hN) w).lower.word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (qEdgeOwner S j a.1 a.2.1) := by
    rw [step_rx S N sigma tau (rxIndex N j hN) (rx_even N j hN) w]
    exact hs0
  have heq : hammingSupport (middle S N sigma tau j hN w).word=
      hammingSupport (step S N sigma tau (rxIndex N j hN) w).lower.word :=
    eq_of_heq (localized_support_cast (index_pair N j hN)
      (step S N sigma tau (rxIndex N j hN) w).lower)
  intro r hr
  exact hs (Eq.mp (congrArg (fun a : Finset (Physical S (2*j+4)) => r∈a) heq) hr)

/-- Both coefficients are derived from the original word; no scalar1 hypothesis. -/
theorem pair_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : hammingSupport w.word ⊆ {seedPhysical S j a}) :
    hammingSupport (pairResult S N sigma tau j hN w).lower.word ⊆ {a.1} := by
  obtain ⟨c,hc⟩ := scalar_singleton w.word _ hw
  rcases bit_cases c with rfl | rfl
  · have hw0 : w.word=0 := hc.trans (scalar_zero _)
    have hm0 : (middle S N sigma tau j hN w).word=0 :=
      localized_cast_zero (index_pair N j hN)
        (step S N sigma tau (rxIndex N j hN) w).lower
          (step_zero S N sigma tau (rxIndex N j hN) w hw0)
    have hl := step_zero S N sigma tau (rzIndex N j hN) _ hm0
    change hammingSupport (step S N sigma tau (rzIndex N j hN)
      (middle S N sigma tau j hN w)).lower.word ⊆ _
    rw [hl]
    simp [hammingSupport]
  · have hw1 : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a) :=
      hc.trans (scalar_one _)
    have hs := intermediate_supported S N sigma tau j hN a w hw1
    have he : BDL26RZPhysicalXStarTransport.Localized S (N+2)
        (Edge N (rzIndex N j hN)) (qEdgeOwner S j a.1 a.2.1)
        (first S N sigma (rzIndex N j hN))
        (second S N sigma tau (rzIndex N j hN) (middle S N sigma tau j hN w)) := by
      change hammingSupport (first S N sigma (rzIndex N j hN)+
        second S N sigma tau (rzIndex N j hN) (middle S N sigma tau j hN w)) ⊆ _
      rw [representatives_difference]
      exact hs
    have hl := BDL26RZPhysicalXStarTransport.lower_supported S (N+2)
      (Edge N (rzIndex N j hN)) (rz_odd N j hN) (by change 3≤2*j+3; omega)
      (qEdgeOwner S j a.1 a.2.1) _ _ he
    have hq := (BDL26RZPhysicalXStarTransport.q_edge_data S (N+2)
      (Edge N (rzIndex N j hN)) (rz_odd N j hN) a.1 a.2.1).1
    rw [← owner_ambient S N j hN a.1 a.2.1] at hq
    rw [hq] at hl
    unfold pairResult
    rw [step_rz S N sigma tau (rzIndex N j hN) (rz_odd N j hN)]
    exact hl

/-- Every original correction interval and the literal adjacent pair of Phi. -/
theorem window_potential (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3≤N) :
    intervalPotential S N sigma tau top (rzIndex N j hN).castSucc (rxIndex N j hN).succ=
      edgePotential S N sigma tau top (rxIndex N j hN)+
        ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
          ((index_pair N j hN).symm ▸ edgePotential S N sigma tau top (rzIndex N j hN)) :=
  adjacent_potential_pair S N sigma tau top _ _ (index_pair N j hN).symm

theorem window_equation (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3≤N) :
    intervalMap1 (SuffixData S N) (rzIndex N j hN).castSucc (rxIndex N j hN).succ
      (by change 2*j+1≤2*j+3; omega)
      (path S N sigma tau top (rzIndex N j hN).castSucc).word=
      (path S N sigma tau top (rxIndex N j hN).succ).word+
        correctionIntervalSum S N sigma (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        correctionIntervalSum S N tau (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        (SuffixData S N).family.coboundary0 (rxIndex N j hN).succ
          (edgePotential S N sigma tau top (rxIndex N j hN)+
            ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
              ((index_pair N j hN).symm ▸ edgePotential S N sigma tau top (rzIndex N j hN))) :=
  interior_pair_equation S N sigma tau top _ _ (index_pair N j hN).symm

/-- Pair recursion is an interval of the SAME original fixed-N path. -/
theorem path_cast (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) {a b : LevelIndex N} (hab : a=b) :
    cast (congrArg (LocalizedWord S N sigma tau) hab) (path S N sigma tau top a)=
      path S N sigma tau top b := by
  cases hab
  rfl

theorem pair_original_steps (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :
    (pairResult S N sigma tau j hN w).lower=
      (step S N sigma tau (rzIndex N j hN)
        (step S N sigma tau (rxIndex N j hN) w).lower).lower := by
  unfold pairResult
  have hm : middle S N sigma tau j hN w=
      (show LocalizedWord S N sigma tau (rzIndex N j hN).succ from
        (step S N sigma tau (rxIndex N j hN) w).lower) :=
    eq_of_heq (cast_heq _ _)
  rw [hm]

theorem pair_original_path (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3≤N) :
    (pairResult S N sigma tau j hN (path S N sigma tau top (rxIndex N j hN).succ)).lower=
      path S N sigma tau top (rzIndex N j hN).castSucc := by
  unfold pairResult middle
  have hmiddle : cast (congrArg (LocalizedWord S N sigma tau) (index_pair N j hN))
      (step S N sigma tau (rxIndex N j hN)
        (path S N sigma tau top (rxIndex N j hN).succ)).lower=
      path S N sigma tau top (rzIndex N j hN).succ := by
    rw [← path_step]
    exact path_cast S N sigma tau top (index_pair N j hN)
  rw [hmiddle,← path_step]

end QEC.Coding.BDL26RXQEdgePairTransport
