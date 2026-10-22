import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXPhysicalCoordinateTrace.Semantics

/-!
# Necessary primitive RX-edge localization

Project-derived internal refinement of BDL26 paper.tex3398-3418,3445-3480,
SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b.
All paths and snapshots use the ORIGINAL total depth and BOTH original histories.
The residual classes are geometric; no reachable decoder failure is asserted.
The original SECOND remains unrestricted and is never identified with a residual
snapshot syndrome. Every full potential includes both stored base calls and the
entire original accumulated potential. The C2 stopping boundary is retained.
-/
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators

theorem zero_boundary (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    (SuffixData S N).family.coboundary0 a 0=
      (BDL26BoundaryTailInvariance.snapshot S N u q a).word :=
  (map_zero _).trans hz.symm

/-- A zero snapshot retains the possibly nonzero common ORIGINAL base calls. -/
theorem zero_base_calls (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    firstReadout S N u=secondReadout S N u q ∧
      (actualBase S N).decode (actualInputs S N (input S N u) 0)=
        (actualBase S N).decode
          (actualInputs S N (perturbTop S N (input S N u) (flip S N q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S N u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S N u q) :=
  BDL26BoundaryTailInvariance.physical_base_calls S N u q a 0
    (zero_boundary S N u q a hz)

def zeroFullPotential (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :=
  BDL26BoundaryTailInvariance.physicalPotential S N u q a 0 (zero_boundary S N u q a hz)

theorem zero_full_formula (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    zeroFullPotential S N u q a hz=
      intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _)
        (BDL26BoundaryTailInvariance.tailPotential S N
          (input S N u) (perturbTop S N (input S N u) (flip S N q))
          (BDL26BoundaryTailInvariance.physicalTop S N u q) a 0
          (zero_boundary S N u q a hz) 0 (Nat.zero_le _))+accumulated S N u q :=
  BDL26BoundaryTailInvariance.physical_potential_formula S N u q a 0
    (zero_boundary S N u q a hz)

theorem zero_full_spec (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (zeroFullPotential S N u q a hz)=
      BDL26LogicalDefectProtection.deltaX S N u q :=
  BDL26BoundaryTailInvariance.physical_potential_spec S N u q a 0
    (zero_boundary S N u q a hz)

theorem zero_chiX (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    BDL26LogicalDefectProtection.chiX S N u q=0 :=
  BDL26BoundaryTailInvariance.physical_chiX_zero S N u q a 0
    (zero_boundary S N u q a hz)

theorem zero_correction_equation (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (zeroFullPotential S N u q a hz)=
      flip S N q+xCorrection S N u+xCorrection S N (translateX S N u (flip S N q)) := by
  rw [zero_full_spec S N u q a hz]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

/-- Safe geometry derives success of the actual ORIGINAL SECOND internally. -/
theorem safe_search (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S N u q) := by
  have hm := parser_semantics S N u q
  cases hl : parse S N q with
  | c2 r =>
    rw [hl] at hm
    have he := c2_singleton_local S N u q r hm
    apply (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    exact ⟨(descent S N u q).word,he,
      BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs⟩
  | face a =>
    rw [hl] at hm
    have he := c2_face_local S N u q a hm
    apply (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    exact ⟨(descent S N u q).word,he,
      BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs⟩
  | killed b =>
    rw [hl] at hm
    obtain ⟨hb,hz⟩ := hm
    have hc := (zero_base_calls S N u q ⟨b,Nat.lt_succ_of_le hb⟩ hz).1
    have ht : secondReadout S N u q=0 := hc.symm.trans hs
    rw [ht]
    exact BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  | primitive p =>
    rw [hl] at hSafe
    cases hSafe

def safeFullPotential (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :=
  BDL26LocalSearchFailureReduction.fullPotential S N u q hs (safe_search S N u q hs hSafe)

theorem safe_base_identity (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    (SuffixData S N).family.coboundary0 0
      (BDL26LocalSearchFailureReduction.basePotential S N u q hs (safe_search S N u q hs hSafe))=
      (descent S N u q).word+
        (actualBase S N).decode (actualInputs S N (input S N u) 0)+
        (actualBase S N).decode
          (actualInputs S N (perturbTop S N (input S N u) (flip S N q)) 0) :=
  BDL26LocalSearchFailureReduction.basePotential_spec S N u q hs (safe_search S N u q hs hSafe)

theorem safe_full_formula (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    safeFullPotential S N u q hs hSafe=
      intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _)
        (BDL26LocalSearchFailureReduction.basePotential S N u q hs
          (safe_search S N u q hs hSafe))+accumulated S N u q := rfl

theorem safe_full_spec (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (safeFullPotential S N u q hs hSafe)=
      BDL26LogicalDefectProtection.deltaX S N u q :=
  BDL26LocalSearchFailureReduction.fullPotential_spec S N u q hs (safe_search S N u q hs hSafe)

theorem safe_correction_equation (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (safeFullPotential S N u q hs hSafe)=
      flip S N q+xCorrection S N u+xCorrection S N (translateX S N u (flip S N q)) :=
  BDL26LocalSearchFailureReduction.original_correction_equation S N u q hs
    (safe_search S N u q hs hSafe)

theorem safe_chiX_zero (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) : BDL26LogicalDefectProtection.chiX S N u q=0 :=
  BDL26LocalSearchFailureReduction.successful_chiX_zero S N u q hs (safe_search S N u q hs hSafe)

/-- The primitive snapshot is an exact nonzero basis word in the ORIGINAL path. -/
theorem first_zero_primitive (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    ∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical := by
  have hn : (parse S N q).safe≠true := by
    intro ht
    exact one_ne_zero (hc.symm.trans (safe_chiX_zero S N u q hs ht))
  have hm := parser_semantics S N u q
  cases hl : parse S N q with
  | c2 r => exact False.elim (hn (by simp only [hl,Leaf.safe]))
  | face a => exact False.elim (hn (by simp only [hl,Leaf.safe]))
  | killed b => exact False.elim (hn (by simp only [hl,Leaf.safe]))
  | @primitive b p =>
    rw [hl] at hm
    obtain ⟨hb,hw⟩ := hm
    obtain ⟨c,hcword⟩ := BDL26RXQEdgePairTransport.scalar_singleton
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word
      p.physical hw
    rcases BDL26RXQEdgePairTransport.bit_cases c with rfl | rfl
    · have hz := hcword.trans (BDL26RXQEdgePairTransport.scalar_zero _)
      exact False.elim (one_ne_zero (hc.symm.trans (zero_chiX S N u q _ hz)))
    · exact ⟨b,hb,p,rfl,hcword.trans (BDL26RXQEdgePairTransport.scalar_one _)⟩

/-- The stored snapshot is the existing actualDescent with the original top input. -/
theorem first_zero_original_snapshot (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    ∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (actualDescent S N (input S N u) (flip S N q) (elementaryCenter S N q)
        (BDL26BoundaryTailInvariance.physical_supported S N q) ⟨b,Nat.lt_succ_of_le hb⟩).word=
          canonicalBasisWord (F:=F) p.physical := by
  obtain ⟨b,hb,p,hp,hw⟩ := first_zero_primitive S N u q hs hc
  refine ⟨b,hb,p,hp,?_⟩
  rw [← BDL26BoundaryTailInvariance.snapshot_original]
  exact hw

/-- Original SECOND failure excludes ALL local owners, independently of the leaf syndrome. -/
theorem first_zero_failure_package (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    (∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical) ∧
    BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S N u q)=none ∧
    (¬∃ e : BDL26LevelTwoLocalBranchEndpoint.Error S, levelTwoLocalError S e ∧
      BDL26LevelTwoLocalBranchEndpoint.delta S e=secondReadout S N u q) ∧
    secondReadout S N u q≠0 :=
  ⟨first_zero_primitive S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_search_none S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_no_local_preimage S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_second_nonzero S N u q hs hc⟩

theorem chiX_one_alternative (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    firstReadout S N u≠0 ∨ ∃ (b : Nat) (hb : b≤N) (p : Primitive S b),
      parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical := by
  by_cases hs : firstReadout S N u=0
  · exact Or.inr (first_zero_primitive S N u q hs hc)
  · exact Or.inl hs

theorem source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧ (firstReadout S (2*(k-1)) u≠0 ∨
      ∃ (b : Nat) (hb : b≤2*(k-1)) (p : Primitive S b),
        parse S (2*(k-1)) q=.primitive p ∧
        (BDL26BoundaryTailInvariance.snapshot S (2*(k-1)) u q
          ⟨b,Nat.lt_succ_of_le hb⟩).word=canonicalBasisWord (F:=F) p.physical) :=
  ⟨by omega,chiX_one_alternative S _ u q hc⟩

/-- Actual finite inputs localized necessarily; no converse reachability is encoded. -/
def primitiveEvent (S : OddScale) (N : Nat) : Finset (XSyndromeDomain S N) :=
  Finset.univ.filter (fun u => firstReadout S N u=0 ∧
    ∃ (q : Physical S (N+2)) (b : Nat) (hb : b≤N) (p : Primitive S b),
      parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical)

theorem mem_primitiveEvent (S : OddScale) (N : Nat) (u : XSyndromeDomain S N) :
    u∈primitiveEvent S N ↔ firstReadout S N u=0 ∧
      ∃ (q : Physical S (N+2)) (b : Nat) (hb : b≤N) (p : Primitive S b),
        parse S N q=.primitive p ∧
        (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
          canonicalBasisWord (F:=F) p.physical := by
  simp only [primitiveEvent,Finset.mem_filter,Finset.mem_univ,true_and]

theorem badX_first_zero_localized (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (hu : u∈BDL26LogicalDefectProtection.badX S N) (hs : firstReadout S N u=0) :
    ∃ (q : Physical S (N+2)) (b : Nat) (hb : b≤N) (p : Primitive S b),
      1≤b ∧ ¬b%2=0 ∧
      BDL26LogicalDefectProtection.chiX S N u q=1 ∧ parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical := by
  have hbad : ¬∀ q : Physical S (N+2), BDL26LogicalDefectProtection.chiX S N u q=0 := by
    simpa only [BDL26LogicalDefectProtection.badX,BDL26LogicalDefectProtection.goodX,
      Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  push_neg at hbad
  obtain ⟨q,hq⟩ := hbad
  have hc := zmod_two_eq_one_of_ne_zero hq
  obtain ⟨b,hb,p,hp,hw⟩ := first_zero_primitive S N u q hs hc
  exact ⟨q,b,hb,p,primitive_positive p,primitive_odd p,hc,hp,hw⟩

theorem badX_subset_events (S : OddScale) (N : Nat) :
    BDL26LogicalDefectProtection.badX S N ⊆
      BDL26LocalSearchFailureReduction.firstEvent S N ∪ primitiveEvent S N := by
  intro u hu
  by_cases hs : firstReadout S N u=0
  · obtain ⟨q,b,hb,p,hpos,hodd,hc,hp,hw⟩ := badX_first_zero_localized S N u hu hs
    exact Finset.mem_union.mpr (Or.inr ((mem_primitiveEvent S N u).mpr ⟨hs,q,b,hb,p,hp,hw⟩))
  · exact Finset.mem_union.mpr
      (Or.inl ((BDL26LocalSearchFailureReduction.mem_firstEvent S N u).mpr hs))

open QEC.Semantics BDL26PairedDecoderPhase

theorem paired_X_zero (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LogicalDefectProtection.dX S N s (CSSDaviesLocality.singlePauli q .x)=0 :=
  BDL26LocalSearchFailureReduction.paired_X_zero S N s q hs (safe_search S N s.1 q hs hSafe)

theorem paired_Y_zero (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LogicalDefectProtection.dX S N s (CSSDaviesLocality.singlePauli q .y)=0 :=
  BDL26LocalSearchFailureReduction.paired_Y_zero S N s q hs (safe_search S N s.1 q hs hSafe)

theorem physical_X_dressed_Z (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S N s=0 :=
  BDL26LocalSearchFailureReduction.physical_X_dressed_Z S N s q hs (safe_search S N s.1 q hs hSafe)

theorem physical_Y_dressed_Z (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S N s=0 :=
  BDL26LocalSearchFailureReduction.physical_Y_dressed_Z S N s q hs (safe_search S N s.1 q hs hSafe)

theorem actual_X_dressed_Z (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    (BDL26CSSDaviesLocality.coupling S (N+2) q .x*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*BDL26CSSDaviesLocality.coupling S (N+2) q .x)*
      atom S N s=0 :=
  BDL26LocalSearchFailureReduction.actual_X_dressed_Z S N s q hs (safe_search S N s.1 q hs hSafe)

theorem actual_Y_package (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (N+2) q .y*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*BDL26CSSDaviesLocality.coupling S (N+2) q .y)*
      atom S N s=0 :=
  BDL26LocalSearchFailureReduction.actual_Y_package S N s q hs (safe_search S N s.1 q hs hSafe)

end QEC.Coding.BDL26RXPrimitiveFailureLocalization
