import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroFaceEndpoint

/-!
# All-coordinate reduction to the original C2 local-search failure

Internal refinement of BDL26 paper.tex3398–3418,3467–3480,3486–3500
(SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
All three actual C2 X-star constructors are exhausted. The original returned
word may have a different owner. Both original base calls and every original
history potential are retained. This is a necessary-failure reduction, not
universal FIRST-zero stability, fallback correctness or a reachability claim.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalSearchFailureReduction

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

abbrev C (S : OddScale) := RawTwo S
abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Syndrome (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Syndrome S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev localSearch (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.localSearch S
abbrev localSuccess (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.localSuccess S

/-- The complete ORIGINAL returned word and BOTH derived predicate clauses. -/
theorem returned_record (S : OddScale) (t : Syndrome S)
    (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    D S t=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S t) ∧ delta S (D S t)=t :=
  ⟨BDL26LevelTwoLocalBranchEndpoint.returned_word S t w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S t w hw⟩

private theorem presentation_operations_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar U)
      (BDL26RXPhysicalStarTransport.physicalXStar V) ∧
    HEq (fun w : Word F U.Q => hammingSupport w)
      (fun w : Word F V.Q => hammingSupport w) ∧
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) ∧
    HEq (tannerCoboundary1 U) (tannerCoboundary1 V) := by
  cases e
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

private theorem actual_presentation (S : OddScale) : (state S 2).presentation=C S :=
  congrArg ConstructionState.presentation (levelTwoState_eq_pair S)

private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (presentation_operations_heq (actual_presentation S)).2.2.1

/-- Relative exactness transports entire operations before choosing an old-X tag. -/
private theorem raw_oldX_two_local (S : OddScale) :
    ∀ (x : (RawOne S).X) (c : BDL26FiniteTannerSquare.Two) (h d e : Error S),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (.inr (x,c)) →
      levelTwoLocalError S d → levelTwoLocalError S e → delta S (h+d+e)=0 →
      ∃ p : Potential S, boundary S p=h+d+e := by
  have ht : ∀ (x : (levelOnePresentation S).X) (c : BDL26FiniteTannerSquare.Two)
      (h d e : Word F (levelTwoPresentation S).Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (levelTwoPresentation S) (.inr (x,c)) →
      levelTwoLocalError S d → levelTwoLocalError S e →
      tannerCoboundary1 (levelTwoPresentation S) (h+d+e)=0 →
      ∃ p : Word F (levelTwoPresentation S).X,
        tannerCoboundary0 (levelTwoPresentation S) p=h+d+e := by
    intro x c h d e hh hd he hc
    obtain ⟨g,edges,faces,hp⟩ :=
      BDL26LevelTwoOldXStarEndpoint.oldX_two_local_full_potential S x c h d e hh hd he hc
    exact ⟨_,hp⟩
  have hp : levelTwoPresentation S=C S :=
    congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
  have hm := presentation_operations_heq hp
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (levelTwoPresentation S) :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) := eq_of_heq hm.2.1
  have hdelta0 : (tannerCoboundary0 (levelTwoPresentation S) :
      Potential S →ₗ[F] Error S)=boundary S := eq_of_heq hm.2.2.1
  have hdelta1 : (tannerCoboundary1 (levelTwoPresentation S) :
      Error S →ₗ[F] Syndrome S)=delta S := eq_of_heq hm.2.2.2
  intro x c h d e hh hd he hc
  have hhs := congrArg (fun support : Error S → Finset (C S).Q => support h) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q => star (.inr (x,c))) hstar
  have hh' : (fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) h ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (levelTwoPresentation S) (.inr (x,c)) := by
    intro r hr
    have hri := Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
    exact Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) (hh hri)
  have hc' : tannerCoboundary1 (levelTwoPresentation S) (h+d+e)=0 :=
    (LinearMap.congr_fun hdelta1 (h+d+e)).trans hc
  obtain ⟨p,hp⟩ := ht x c h d e hh' hd he hc'
  exact ⟨p,(LinearMap.congr_fun hdelta0 p).symm.trans hp⟩

/-- Every full raw C2 star, including both old-X copies; no locality of h is assumed. -/
theorem raw_star_endpoint (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by
  change RZX (RawOne S) S at x
  rcases x with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · exact BDL26LevelTwoLocalBranchEndpoint.face_endpoint S z f h hh hb
  · exact BDL26LevelTwoLocalBranchEndpoint.edge_endpoint S q e h hh hb
  · obtain ⟨w,hw⟩ := hb
    have hr := returned_record S (delta S h) w hw
    have hz : D S (0 : Syndrome S)=(0 : Error S) :=
      BDL26LevelTwoLocalBranchEndpoint.decode_zero S
    have hd : levelTwoLocalError S (D S 0) :=
      Eq.mpr (congrArg (fun a : Error S => levelTwoLocalError S a) hz)
        (zero_original_local S)
    have hdz : delta S (D S 0)=0 := (congrArg (delta S) hz).trans (map_zero _)
    have hc : delta S (h+D S 0+D S (delta S h))=0 := by
      rw [map_add,map_add,hdz,hr.2.2,add_zero]
      exact ZModModule.add_self _
    exact raw_oldX_two_local S x c h _ _ hh hd hr.2.1 hc

def rawStarPotential (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) : Potential S :=
  Classical.choose (raw_star_endpoint S x h hh hb)

theorem rawStarPotential_spec (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) :
    boundary S (rawStarPotential S x h hh hb)=h+D S 0+D S (delta S h) :=
  Classical.choose_spec (raw_star_endpoint S x h hh hb)

/-- Transport the whole computed centre, without a constructor/local-owner premise. -/
theorem terminal_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    hammingSupport (descent S n u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (C S) (descent S n u q).center := by
  have hm := presentation_operations_heq (actual_presentation S)
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) := eq_of_heq hm.2.1
  have hh := descent_supported S n u q
  change (fun w : Word F (state S 2).presentation.Q => hammingSupport w)
      (descent S n u q).word ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (descent S n u q).center at hh
  have hhs := congrArg (fun support : Error S → Finset (C S).Q =>
    support (descent S n u q).word) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q =>
    star (descent S n u q).center) hstar
  intro r hr
  have hri := Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
  exact Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) (hh hri)

/-- FIRST zero identifies the raw terminal syndrome with the unrestricted SECOND. -/
theorem terminal_search (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    localSuccess S (delta S (descent S n u q).word) := by
  rw [BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs]
  exact hb

/-- Complete actual SECOND returned record; neither its word nor its owner is replaced. -/
theorem second_returned_record (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hb : localSuccess S (secondReadout S n u q)) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      localSearch S (secondReadout S n u q)=some w ∧
      D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S n u q)) ∧
      delta S (D S (secondReadout S n u q))=secondReadout S n u q := by
  obtain ⟨w,hw⟩ := hb
  exact ⟨w,hw,returned_record S _ w hw⟩

def basePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) : (SuffixData S n).family.Cochain0 0 :=
  rawStarPotential S (descent S n u q).center (descent S n u q).word
    (terminal_supported S n u q) (terminal_search S n u q hs hb)

/-- Both literal stored base calls occur in the full base residual. -/
theorem basePotential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    (SuffixData S n).family.coboundary0 0 (basePotential S n u q hs hb)=
      (descent S n u q).word+
        (actualBase S n).decode (actualInputs S n (input S n u) 0)+
        (actualBase S n).decode
          (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0) := by
  have hp := rawStarPotential_spec S (descent S n u q).center (descent S n u q).word
    (terminal_supported S n u q) (terminal_search S n u q hs hb)
  rw [BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs] at hp
  have he := LinearMap.congr_fun (actual_delta0 S) (basePotential S n u q hs hb)
  have hfirst : (actualBase S n).decode (actualInputs S n (input S n u) 0)=D S 0 :=
    (first_base_original_D S n u).trans (congrArg (D S) hs)
  have hsecond : (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
      D S (secondReadout S n u q) := second_base_original_D S n u q
  let h : Error S := (descent S n u q).word
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hfilled := hp.trans hcalls
  have hbase : (SuffixData S n).family.coboundary0 0 (basePotential S n u q hs hb)=
      boundary S (basePotential S n u q hs hb) := by
    rw [suffix_delta0]
    exact he
  exact hbase.trans hfilled

/-- The entire original accumulated potential, without truncation or zeroing Phi. -/
def fullPotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (basePotential S n u q hs hb)+accumulated S n u q

theorem fullPotential_formula (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    fullPotential S n u q hs hb=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (basePotential S n u q hs hb)+accumulated S n u q := rfl

theorem fullPotential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q hs hb)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    basePotential_spec S n u q hs hb]
  exact (full_history S n u q).symm

theorem original_correction_equation (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q hs hb)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [fullPotential_spec S n u q hs hb]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

/-- Successful original SECOND is sufficient for the actual X logical bit to vanish. -/
theorem successful_chiX_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨fullPotential S n u q hs hb,?_⟩
  rw [full_residual]
  exact fullPotential_spec S n u q hs hb

/-- Public Option-valued version consumes the actual returned word. -/
theorem some_chiX_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S (secondReadout S n u q)=some w) :
    BDL26LogicalDefectProtection.chiX S n u q=0 :=
  successful_chiX_zero S n u q hs ⟨w,hw⟩

/-- Unconditional necessary failure alternative for EVERY actual coordinate. -/
theorem chiX_one_search_failure (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    firstReadout S n u≠0 ∨ localSearch S (secondReadout S n u q)=none := by
  by_cases hs : firstReadout S n u=0
  · right
    cases ht : localSearch S (secondReadout S n u q) with
    | none => rfl
    | some w =>
      exact False.elim (one_ne_zero (hc.symm.trans (some_chiX_zero S n u q hs w ht)))
  · exact Or.inl hs

theorem first_zero_search_none (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    localSearch S (secondReadout S n u q)=none :=
  (chiX_one_search_failure S n u q hc).resolve_left (fun hn => hn hs)

/-- NONE excludes ALL owner-local representatives of the original SECOND syndrome. -/
theorem first_zero_no_local_preimage (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    ¬∃ e : Error S, levelTwoLocalError S e ∧ delta S e=secondReadout S n u q :=
  (BDL26LevelTwoLocalBranchEndpoint.localSearch_none_iff S _).mp
    (first_zero_search_none S n u q hs hc)

theorem search_none_nonzero (S : OddScale) (t : Syndrome S)
    (hn : localSearch S t=none) : t≠0 := by
  intro ht
  rw [ht] at hn
  obtain ⟨w,hw⟩ := BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  have hw' : localSearch S (0 : Syndrome S)=some w := hw
  have hnone : (none : Option (Word F (BDL26LevelTwoDecoder.ExecutableQ S)))=some w :=
    hn.symm.trans hw'
  cases hnone

/-- This consequence does not classify the unfiltered fallback as logically wrong. -/
theorem first_zero_second_nonzero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) : secondReadout S n u q≠0 :=
  search_none_nonzero S _ (first_zero_search_none S n u q hs hc)

/-- Source-even k1/C2 is included in the same necessary-failure statement. -/
theorem source_even (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧
      (firstReadout S (2*(k-1)) u≠0 ∨ localSearch S (secondReadout S (2*(k-1)) u q)=none) :=
  ⟨by omega,chiX_one_search_failure S _ u q hc⟩

/-- Finite events are derived from actual inputs; they store no stability claim. -/
def firstEvent (S : OddScale) (n : Nat) : Finset (XSyndromeDomain S n) :=
  Finset.univ.filter (fun u => firstReadout S n u≠0)

def searchFailureEvent (S : OddScale) (n : Nat) : Finset (XSyndromeDomain S n) :=
  Finset.univ.filter (fun u => firstReadout S n u=0 ∧
    ∃ q : Physical S (n+2), localSearch S (secondReadout S n u q)=none)

theorem mem_firstEvent (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    u ∈ firstEvent S n ↔ firstReadout S n u≠0 := by
  simp only [firstEvent,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_searchFailureEvent (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    u ∈ searchFailureEvent S n ↔ firstReadout S n u=0 ∧
      ∃ q : Physical S (n+2), localSearch S (secondReadout S n u q)=none := by
  simp only [searchFailureEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- A second unresolved event is kept; this is NOT badX bounded by FIRST alone. -/
theorem badX_subset_events (S : OddScale) (n : Nat) :
    BDL26LogicalDefectProtection.badX S n ⊆ firstEvent S n ∪ searchFailureEvent S n := by
  intro u hu
  have hbad : ¬∀ q : Physical S (n+2), BDL26LogicalDefectProtection.chiX S n u q=0 := by
    simpa only [BDL26LogicalDefectProtection.badX,BDL26LogicalDefectProtection.goodX,
      Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  push_neg at hbad
  obtain ⟨q,hq⟩ := hbad
  have hc : BDL26LogicalDefectProtection.chiX S n u q=1 := zmod_two_eq_one_of_ne_zero hq
  by_cases hs : firstReadout S n u=0
  · apply Finset.mem_union.mpr
    right
    exact (mem_searchFailureEvent S n u).mpr ⟨hs,q,first_zero_search_none S n u q hs hc⟩
  · exact Finset.mem_union.mpr (Or.inl ((mem_firstEvent S n u).mpr hs))

open QEC.Semantics BDL26PairedDecoderPhase

theorem paired_X_zero (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 := by
  rw [paired_X_bit]
  exact successful_chiX_zero S n s.1 q hs hb

theorem paired_Y_zero (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=0 := by
  rw [paired_Y_bit]
  exact successful_chiX_zero S n s.1 q hs hb

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  exact paired_X_zero S n s q hs hb

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  exact paired_Y_zero S n s q hs hb

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*
      atom S n s=0 := physical_X_dressed_Z S n s q hs hb

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*
      atom S n s=0 := physical_Y_dressed_Z S n s q hs hb

/-- Same genuine Y=iXZ coupling and actual SAME-Y dressed-Z consumer. -/
theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*
      atom S n s=0 :=
  ⟨physical_Y_iXZ S n q,actual_Y_dressed_Z S n s q hs hb⟩

end QEC.Coding.BDL26LocalSearchFailureReduction
