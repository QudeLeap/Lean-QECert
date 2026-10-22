import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroEmptySuffix

/-!
# FIRST-zero stability for actual Q-vertex towers

Project-derived internal restriction of BDL26 paper.tex3383–3484. A tower is
generated only by actual successor Q-vertex constructors, with every cylinder
vertex and both copies retained. At one fixed total depth the SAME original
two histories descend to a scalar times the inherited C2 basis coordinate.
The original RX zero-potential branch is evaluated; the entire original RZ
potential and both base calls remain. FIRST alone is zero. This is a proper
coordinate subfamily at positive depth, not general Q-edge/old-X stability,
chiZ/XYZ, ALL-component locality, Peierls, Gibbs or lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev Edge (n : Nat) (i : StepIndex n) := BDL26LocalizedHistoryErrorDescent.Edge n i

private theorem word_smul_zero {I : Type} (w : Word F I) : (0 : F) • w=0 := by
  funext r
  exact zero_mul _

private theorem word_smul_one {I : Type} (w : Word F I) : (1 : F) • w=w := by
  funext r
  exact one_mul _

private theorem bit_cases (c : F) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem scalar_singleton {I : Type} [Fintype I] [DecidableEq I]
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

private theorem basis_singleton {I : Type} [Fintype I] [DecidableEq I] (q : I) :
    hammingSupport (canonicalBasisWord (F:=F) q) ⊆ {q} := by
  intro r hr
  by_contra hn
  have hne : r≠q := by simpa only [Finset.mem_singleton] using hn
  have hz : canonicalBasisWord (F:=F) q r=0 := by simp [canonicalBasisWord,hne]
  exact (Finset.mem_filter.mp hr).2 hz

/-- The actual RX Q-vertex summand, using the original successor equality. -/
def rxVertex (S : OddScale) (m : Nat) (h : m%2=0)
    (q : Physical S m) (v : QDoubleCylinderVertex (state S m).presentation q S) :
    Physical S (m+1) :=
  (BDL26RXDecoderAdapter.rxQVertexEquiv S (m+1) ⟨m,Nat.lt_succ_self m⟩ h q v).val

/-- The actual RZ Q-vertex summand, including every transposed vertex/copy. -/
def rzVertex (S : OddScale) (m : Nat) (h : ¬m%2=0)
    (q : Physical S m)
    (v : QDoubleCylinderVertex (transposePresentation (state S m).presentation) q S) :
    Physical S (m+1) :=
  BDL26RZPhysicalStarTransport.physicalQ S (m+1) ⟨m,Nat.lt_succ_self m⟩ h q v

/-- Generated physical constructor data, containing no locality or proof endpoint. -/
inductive Tower (S : OddScale) : (n : Nat) → Physical S (n+2) → Type
  | base (q : Physical S 2) : Tower S 0 q
  | rx {n : Nat} {q : Physical S (n+2)} (t : Tower S n q)
      (h : (n+2)%2=0)
      (v : QDoubleCylinderVertex (state S (n+2)).presentation q S) :
      Tower S (n+1) (rxVertex S (n+2) h q v)
  | rz {n : Nat} {q : Physical S (n+2)} (t : Tower S n q)
      (h : ¬(n+2)%2=0)
      (v : QDoubleCylinderVertex (transposePresentation (state S (n+2)).presentation) q S) :
      Tower S (n+1) (rzVertex S (n+2) h q v)

/-- The inherited actual C2 coordinate is computed from constructor data. -/
def bottom {S : OddScale} {n : Nat} {q : Physical S (n+2)} : Tower S n q → Physical S 2
  | .base r => r
  | .rx t _ _ => bottom t
  | .rz t _ _ => bottom t

section RX
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val%2=0)
variable (q : (state S i.val).presentation.Q)
variable (a b : BDL26RXErrorPullback.Upper S depth i)
variable (he : hammingSupport (a+b) ⊆
  (BDL26RXDecoderAdapter.rxLq S depth i h).correctionRegion q)
include he

private theorem rx_local_potential_zero (x : (state S i.val).presentation.X) :
    BDL26RXXStarTransport.potential S depth i h x a b=0 := by
  have hu := BDL26RXQBlockTransport.updated_supported S depth i h q a b he
  have hx := BDL26RXQBlockTransport.error_x_zero S depth i h q
    (BDL26RXErrorPullback.updated S depth i h a b) hu x
  unfold BDL26RXXStarTransport.potential BDL26RXXStarTransport.localPotential
  rw [if_pos hx]
  exact map_zero _

/-- Evaluation of the ORIGINAL explicit zero branch, for every actual X set. -/
theorem rx_phi_zero (X0 : Finset (state S i.val).presentation.X) :
    BDL26RXFiniteBlockTransport.Phi S depth i h X0 a b=0 := by
  unfold BDL26RXFiniteBlockTransport.Phi
  apply Finset.sum_eq_zero
  intro x _
  exact rx_local_potential_zero S depth i h q a b he x

/-- The SAME original L is the scalar singleton word, not a replacement inverse. -/
theorem rx_lower_word (X0 : Finset (state S i.val).presentation.X) :
    BDL26RXFiniteBlockTransport.L S depth i h X0 a b=
      BDL26RXQBlockTransport.lowerWord S depth i h q a b := by
  have hz := rx_phi_zero S depth i h q a b he X0
  have hez := rx_phi_zero S depth i h q a b he ∅
  have hl : BDL26RXFiniteBlockTransport.L S depth i h X0 a b=
      BDL26RXFiniteBlockTransport.L S depth i h ∅ a b := by
    unfold BDL26RXFiniteBlockTransport.L
    funext r
    simp only [BDL26RXFiniteBlockTransport.R,hz,hez,map_zero,add_zero]
  apply hl.trans
  apply BDL26RXFiniteBlockTransport.lower_singleton_q S depth i h q a b
  change hammingSupport (a+b) ⊆
    BDL26RXFiniteBlockTransport.xBlocks S depth i h ∅ ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h {q}
  simpa [BDL26RXFiniteBlockTransport.xBlocks,BDL26RXFiniteBlockTransport.qBlocks] using he

/-- The original computed parentX is retained when its chosen potential is zero. -/
theorem rx_computed_parent (u : FamilyX S depth i.succ) :
    BDL26RXPhysicalStarTransport.Phi S depth i h u a b=0 ∧
    BDL26RXPhysicalStarTransport.L S depth i h u a b=
      BDL26RXQBlockTransport.lowerWord S depth i h q a b := by
  constructor
  · exact rx_phi_zero S depth i h q a b he
      {BDL26RXPhysicalStarTransport.parentX S depth i h u}
  · exact rx_lower_word S depth i h q a b he
      {BDL26RXPhysicalStarTransport.parentX S depth i h u}
end RX

section FixedDepth
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)

private theorem step_rx_singleton (i : StepIndex n) (h : (i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (state S (i.val+2)).presentation q S)
    (hu : hammingSupport u.word ⊆ {rxVertex S (i.val+2) h q v}) :
    (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).potential=0 ∧
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : (Edge n i).val%2=0 := by
    simpa only [Edge,LevelTwoHistory.physicalStep_val] using h
  have he : hammingSupport
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+
        BDL26LocalizedHistoryErrorDescent.second S n sigma tau i u) ⊆
      (BDL26RXDecoderAdapter.rxLq S (n+2) (Edge n i) hh).correctionRegion q := by
    rw [BDL26LocalizedHistoryErrorDescent.representatives_difference]
    intro r hr
    have heq : r=rxVertex S (i.val+2) h q v := Finset.mem_singleton.mp (hu hr)
    subst r
    exact (BDL26RXDecoderAdapter.rxQVertexEquiv S (n+2) (Edge n i) hh q v).property
  have hz := rx_computed_parent S (n+2) (Edge n i) hh q _ _ he u.center
  rw [BDL26LocalizedHistoryErrorDescent.step_rx S n sigma tau i hh u]
  constructor
  · exact hz.1
  · change hammingSupport (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) hh
      u.center _ _) ⊆ {q}
    rw [hz.2]
    exact BDL26RXQBlockTransport.lower_supported S (n+2) (Edge n i) hh q _ _

private theorem step_rz_singleton (i : StepIndex n) (h : ¬(i.val+2)%2=0)
    (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S n sigma tau i.succ)
    (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (transposePresentation (state S (i.val+2)).presentation) q S)
    (hu : hammingSupport u.word ⊆ {rzVertex S (i.val+2) h q v}) :
    hammingSupport (BDL26LocalizedHistoryErrorDescent.step S n sigma tau i u).lower.word ⊆ {q} := by
  have hh : ¬(Edge n i).val%2=0 := by
    simpa only [Edge,LevelTwoHistory.physicalStep_val] using h
  obtain ⟨c,hc⟩ := scalar_singleton u.word _ hu
  have hcases : c=0 ∨ c=1 := bit_cases c
  rw [BDL26LocalizedHistoryErrorDescent.step_rz S n sigma tau i hh u]
  change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) hh
    (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
    (BDL26LocalizedHistoryErrorDescent.second S n sigma tau i u)) ⊆ {q}
  rcases hcases with rfl | rfl
  · have hw : u.word=0 := hc.trans (word_smul_zero _)
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,
      BDL26LocalizedHistoryErrorDescent.representatives_difference,hw,map_zero,map_zero]
    simp [hammingSupport]
  · have hw : u.word=canonicalBasisWord (rzVertex S (i.val+2) h q v) :=
      hc.trans (word_smul_one _)
    have hw' : u.word=(canonicalBasisWord
        (BDL26RZPhysicalStarTransport.physicalQ S (n+2) (Edge n i) hh q v) :
        BDL26RZErrorPullback.Upper S (n+2) (Edge n i)) := hw
    change hammingSupport (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i)
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i+u.word)) ⊆ {q}
    rw [hw']
    have hl := BDL26RZPhysicalStarTransport.lower_physicalQ_basis S (n+2) (Edge n i) hh
      (BDL26LocalizedHistoryErrorDescent.first S n sigma i) q v
    rw [hl]
    exact basis_singleton q

/-- Induction on generated coordinates, keeping total depth and BOTH histories fixed. -/
private theorem tower_down {b : Nat} {q : Physical S (b+2)} (t : Tower S b q) :
    ∀ (total : Nat) (sigma tau : TopInput S total) (hb : b≤total)
      (u : BDL26LocalizedHistoryErrorDescent.LocalizedWord S total sigma tau
        ⟨b,Nat.lt_succ_of_le hb⟩),
      hammingSupport u.word ⊆ {q} →
      hammingSupport (BDL26LocalizedHistoryErrorDescent.down S total sigma tau b hb u 0
        (Nat.zero_le b)).word ⊆ {bottom t} := by
  induction t with
  | base q =>
      intro total sigma tau hb u hu
      change hammingSupport (BDL26LocalizedHistoryErrorDescent.down S total sigma tau 0 hb u
        ⟨0,Nat.lt_succ_of_le hb⟩ (Nat.le_refl 0)).word ⊆ {q}
      rw [BDL26LocalizedHistoryErrorDescent.down_self]
      exact hu
  | @rx b q t h v ih =>
      intro total sigma tau hb u hu
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := (step_rx_singleton S total sigma tau i h u q v hu).2
      rw [BDL26LocalizedHistoryErrorDescent.down_succ S total sigma tau b hb u 0 (Nat.zero_le b)]
      exact ih total sigma tau (by omega) _ hl
  | @rz b q t h v ih =>
      intro total sigma tau hb u hu
      let i : StepIndex total := ⟨b,by omega⟩
      have hl := step_rz_singleton S total sigma tau i h u q v hu
      rw [BDL26LocalizedHistoryErrorDescent.down_succ S total sigma tau b hb u 0 (Nat.zero_le b)]
      exact ih total sigma tau (by omega) _ hl
end FixedDepth

private theorem flip_star_supported (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    hammingSupport (flip S n q) ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n)
      (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact BDL26LocalizedHistoryErrorDescent.elementary_support S n q

/-- Actual descent confinement; no coefficient, terminal centre or FIRST premise. -/
theorem terminal_singleton (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    hammingSupport (descent S n u q).word ⊆ {bottom t} := by
  have hi : hammingSupport
      (BDL26LocalizedHistoryErrorDescent.initial S n (input S n u) (flip S n q)
        (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_star_supported S n q)).word ⊆ {q} := by
    change hammingSupport (flip S n q) ⊆ {q}
    rw [flip_eq_basis]
    exact basis_singleton q
  exact tower_down S t n (input S n u)
    (perturbTop S n (input S n u) (flip S n q)) (Nat.le_refl _) _ hi

/-- The scalar is derived from the actual terminal word, including the zero case. -/
theorem terminal_scalar (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    ∃ c : F, (descent S n u q).word=c • canonicalBasisWord (bottom t) :=
  scalar_singleton _ _ (terminal_singleton S n u q t)

/-- Named raw-carrier view of the actual descent; its value is unchanged. -/
def terminalWord (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) : Error S := (descent S n u q).word

/-- Binary alternatives are conclusions about the actual histories. -/
theorem terminal_cases (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    terminalWord S n u q=0 ∨
      terminalWord S n u q=BDL26FirstZeroEmptySuffix.physicalWord S (bottom t) := by
  obtain ⟨c,hc⟩ := terminal_scalar S n u q t
  have hraw : terminalWord S n u q=c • (canonicalBasisWord (bottom t) : Error S) := hc
  have hcases : c=0 ∨ c=1 := bit_cases c
  rcases hcases with rfl | rfl
  · exact Or.inl (hraw.trans (word_smul_zero _))
  · apply Or.inr
    have hb : BDL26FirstZeroEmptySuffix.physicalWord S (bottom t)=
        (canonicalBasisWord (bottom t) : Error S) := flip_eq_basis S 0 (bottom t)
    exact (hraw.trans (word_smul_one _)).trans hb.symm

/-- The actual terminal correction owner is constructed internally. -/
theorem terminal_local (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    levelTwoLocalError S (terminalWord S n u q) := by
  rcases terminal_cases S n u q t with hz | hb
  · apply (levelTwoLocalError_iff_owner S _).mpr
    refine ⟨BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S (bottom t),?_⟩
    intro r hr
    rw [hz] at hr
    exact False.elim (hr rfl)
  · rw [hb]
    exact BDL26FirstZeroEmptySuffix.physical_flip_local S (bottom t)

/-- The unchanged original first table search succeeds on the actual SECOND input. -/
theorem second_search (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S n u q) := by
  rw [← BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs]
  exact (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨terminalWord S n u q,terminal_local S n u q t,rfl⟩

/-- Keep the actual independently returned word and its derived properties. -/
theorem second_returned (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S n u q)) ∧
      delta S (D S (secondReadout S n u q))=secondReadout S n u q := by
  obtain ⟨w,hw⟩ := second_search S n u q t hs
  exact ⟨w,hw,BDL26LevelTwoLocalBranchEndpoint.returned_word S _ w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw⟩

theorem second_nonzero_output (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0)
    (ht : secondReadout S n u q≠0) : D S (secondReadout S n u q)≠0 :=
  BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output S _
    (second_search S n u q t hs) ht

private theorem terminal_endpoint (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    ∃ p : Potential S, boundary S p=
      terminalWord S n u q+D S 0+D S (delta S (terminalWord S n u q)) := by
  rcases terminal_cases S n u q t with hz | hb
  · refine ⟨0,?_⟩
    simp only [hz,map_zero,BDL26LevelTwoLocalBranchEndpoint.decode_zero,add_zero]
  · obtain ⟨p,hp⟩ := BDL26FirstZeroEmptySuffix.physical_endpoint S (bottom t)
    refine ⟨p,?_⟩
    rw [hb]
    exact hp

/-- Chosen only from the proved endpoint of the actual terminal word. -/
def basePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) : (SuffixData S n).family.Cochain0 0 :=
  Classical.choose (terminal_endpoint S n u q t)

private theorem coboundary0_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by
  cases e
  rfl

private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (coboundary0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

/-- Both stored original base calls, on their literal original input histories. -/
theorem base_history_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      (descent S n u q).word+
        (actualBase S n).decode (actualInputs S n (input S n u) 0)+
        (actualBase S n).decode
          (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0) := by
  have hp : boundary S (basePotential S n u q t)=
      terminalWord S n u q+D S 0+D S (delta S (terminalWord S n u q)) :=
    Classical.choose_spec (terminal_endpoint S n u q t)
  have hd : delta S (terminalWord S n u q)=secondReadout S n u q :=
    BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs
  have hdecode := congrArg (D S) hd
  have hnormalized := congrArg
    (fun d : Error S => terminalWord S n u q+D S 0+d) hdecode
  have hp' := hp.trans hnormalized
  have hfirst : (actualBase S n).decode (actualInputs S n (input S n u) 0)=D S 0 :=
    (first_base_original_D S n u).trans (congrArg (D S) hs)
  have hsecond : (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
        D S (secondReadout S n u q) := second_base_original_D S n u q
  let h : Error S := terminalWord S n u q
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hbase : (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      boundary S (basePotential S n u q t) := by
    rw [suffix_delta0]
    exact LinearMap.congr_fun (actual_delta0 S) (basePotential S n u q t)
  exact hbase.trans (hp'.trans hcalls)

/-- All original accumulated potentials remain, including nonzero RZ choices. -/
def fullPotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (basePotential S n u q t)+
    accumulated S n u q

theorem full_potential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_history_spec S n u q t hs]
  exact (full_history S n u q).symm

theorem original_correction_equation (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [full_potential_spec S n u q t hs]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

theorem first_zero_chiX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨fullPotential S n u q t,?_⟩
  rw [full_residual]
  exact full_potential_spec S n u q t hs

/-- Source-even depth 2k includes the unrestricted C2 base at k=1. -/
theorem source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (t : Tower S (2*(k-1)) q) (hs : firstReadout S (2*(k-1)) u=0) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,first_zero_chiX S _ u q t hs⟩

open QEC.Semantics BDL26PairedDecoderPhase

theorem physical_Y_iXZ (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) :=
  BDL26ActualFailureReadout.physical_Y_iXZ S n q

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S n s.1 q t hs

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_Y_bit]
  exact first_zero_chiX S n s.1 q t hs

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 :=
  physical_X_dressed_Z S n s q t hs

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  physical_Y_dressed_Z S n s q t hs

theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  ⟨physical_Y_iXZ S n q,actual_Y_dressed_Z S n s q t hs⟩

end QEC.Coding.BDL26FirstZeroQVertexTower
