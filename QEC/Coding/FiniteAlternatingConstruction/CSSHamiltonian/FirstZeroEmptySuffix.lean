import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.FirstZeroFaceEndpoint

/-!
# All-coordinate FIRST-zero stability for the actual empty suffix

Project-derived base-case refinement of BDL26 paper.tex3383–3484. Every physical
C2 basis word has its own actual owner, so the unchanged original lookup
succeeds. Both selector outputs and the entire interval potential are retained;
only the FIRST readout is assumed zero. No terminal-constructor or second-zero
premise occurs. This proves neither arbitrary-depth stability nor chiZ, full
XYZ protection, ALL-component locality, probability or lifetime bounds.
-/
noncomputable section
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

abbrev P (S : OddScale) := RawOne S
abbrev C (S : OddScale) := RawTwo S
abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S

/-- The actual recursive C2 carrier is the internally proved RX/RZ-pair carrier. -/
private theorem physical_carrier (S : OddScale) : (C S).Q=Physical S 2 :=
  congrArg (fun st : ConstructionState => st.presentation.Q) (levelTwoState_eq_pair S).symm

/-- Named canonical carrier transport for all raw coordinates. The equivalence
is constructed from the actual state equality, not supplied by a caller. -/
def physicalQubit (S : OddScale) : (C S).Q ≃ Physical S 2 :=
  Equiv.cast (physical_carrier S)

/-- The literal empty descent retains the flip and has no earlier potential. -/
theorem empty_descent (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 :=
  BDL26ActualFailureReadout.empty_suffix S u q

/-- Every physical coordinate has its own derived owner, with no star premise. -/
theorem physical_flip_local (S : OddScale) (q : Physical S 2) :
    levelTwoLocalError S (flip S 0 q) := by
  rw [flip_eq_basis]
  exact BDL26LevelTwoLocalBranchEndpoint.elementary_local S q

/-- The unchanged first table succeeds on every physical elementary syndrome. -/
theorem physical_flip_search (S : OddScale) (q : Physical S 2) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (delta S (flip S 0 q)) :=
  (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨flip S 0 q,physical_flip_local S q,rfl⟩

/-- The literal physical flip on the raw C2 carrier; no representative is chosen. -/
def physicalWord (S : OddScale) (q : Physical S 2) : Error S := flip S 0 q

/-- Complete original elementary endpoint on both physical coordinate constructors. -/
theorem physical_endpoint (S : OddScale) (q : Physical S 2) :
    ∃ p : Potential S, boundary S p=
      physicalWord S q+D S 0+D S (delta S (flip S 0 q)) := by
  obtain ⟨p,hp⟩ := BDL26LevelTwoLocalBranchEndpoint.elementary_endpoint S q
  have he := congrArg (fun w : Error S => w+D S 0+D S (delta S w))
    (flip_eq_basis S 0 q)
  exact ⟨p,hp.trans he.symm⟩

/-- Selected only from the proved full elementary boundary construction. -/
def elementaryPotential (S : OddScale) (q : Physical S 2) :
    (SuffixData S 0).family.Cochain0 0 :=
  Classical.choose (physical_endpoint S q)

theorem base_potential_spec (S : OddScale) (q : Physical S 2) :
    boundary S (elementaryPotential S q)=
      physicalWord S q+D S 0+D S (delta S (flip S 0 q)) :=
  Classical.choose_spec (physical_endpoint S q)

/-- FIRST zero fixes the SECOND input to the syndrome of the actual physical flip. -/
theorem second_syndrome (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    delta S (flip S 0 q)=secondReadout S 0 u q := by
  have hword : (descent S 0 u q).word=(flip S 0 q : Error S) :=
    (empty_descent S u q).1
  exact (congrArg (delta S) hword).symm.trans
    (BDL26FirstZeroFaceEndpoint.terminal_syndrome S 0 u q hs)

/-- Actual SECOND search success is derived, never accepted as caller data. -/
theorem second_search (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S 0 u q) := by
  rw [← second_syndrome S u q hs]
  exact physical_flip_search S q

/-- The actual original returned word is retained without claiming its owner. -/
theorem second_returned (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S 0 u q)=some w ∧
      D S (secondReadout S 0 u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S 0 u q)) ∧
      delta S (D S (secondReadout S 0 u q))=secondReadout S 0 u q := by
  obtain ⟨w,hw⟩ := second_search S u q hs
  exact ⟨w,hw,BDL26LevelTwoLocalBranchEndpoint.returned_word S _ w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw⟩

/-- Nonzero SECOND input keeps a genuinely nonzero original correction. -/
theorem second_nonzero_output (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) (ht : secondReadout S 0 u q≠0) :
    D S (secondReadout S 0 u q)≠0 :=
  BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output S _ (second_search S u q hs) ht

private theorem coboundary0_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by
  cases e
  rfl

private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (coboundary0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

/-- Both stored original base calls occur in the full actual endpoint equation. -/
theorem base_history_spec (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 0 (elementaryPotential S q)=
      (descent S 0 u q).word+
        (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)+
        (actualBase S 0).decode
          (actualInputs S 0 (perturbTop S 0 (input S 0 u) (flip S 0 q)) 0) := by
  have hp := base_potential_spec S q
  rw [second_syndrome S u q hs] at hp
  let h : Error S := (descent S 0 u q).word
  have hflip : (flip S 0 q : Error S)=h := (empty_descent S u q).1.symm
  have hp' := hp.trans
    (congrArg (fun w : Error S => w+D S 0+D S (secondReadout S 0 u q)) hflip)
  have hfirst : (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)=D S 0 := by
    have hcall : (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)=
        D S (firstReadout S 0 u) := first_base_original_D S 0 u
    exact hcall.trans (congrArg (D S) hs)
  have hsecond : (actualBase S 0).decode
      (actualInputs S 0 (perturbTop S 0 (input S 0 u) (flip S 0 q)) 0)=
        D S (secondReadout S 0 u q) := second_base_original_D S 0 u q
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hfilled := hp'.trans hcalls
  have hbase : (SuffixData S 0).family.coboundary0 0 (elementaryPotential S q)=
      boundary S (elementaryPotential S q) := by
    rw [suffix_delta0]
    exact LinearMap.congr_fun (actual_delta0 S) (elementaryPotential S q)
  exact hbase.trans hfilled

/-- The full original formula is kept even though its interval is empty. -/
def fullPotential (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2) :
    (SuffixData S 0).family.Cochain0 (TopIndex 0) :=
  intervalMap0 (SuffixData S 0) 0 (TopIndex 0) (Nat.zero_le _) (elementaryPotential S q)+
    accumulated S 0 u q

theorem full_potential_spec (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 (TopIndex 0) (fullPotential S u q)=
      BDL26LogicalDefectProtection.deltaX S 0 u q := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ 0 (Nat.le_refl _) 0 (Nat.zero_le _),
    base_history_spec S u q hs]
  exact (full_history S 0 u q).symm

/-- The original input and its original translated input retain both corrections. -/
theorem original_correction_equation (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 (TopIndex 0) (fullPotential S u q)=
      flip S 0 q+xCorrection S 0 u+xCorrection S 0 (translateX S 0 u (flip S 0 q)) := by
  rw [full_potential_spec S u q hs]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

/-- All physical coordinates and all scales, without any terminal-constructor premise. -/
theorem first_zero_chiX (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) : BDL26LogicalDefectProtection.chiX S 0 u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S 0 (input S 0 u) (flip S 0 q)).mpr
  refine ⟨fullPotential S u q,?_⟩
  rw [full_residual]
  exact full_potential_spec S u q hs

open QEC.Semantics BDL26PairedDecoderPhase

theorem physical_Y_iXZ (S : OddScale) (q : Physical S 2) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) :=
  BDL26ActualFailureReadout.physical_Y_iXZ S 0 q

theorem physical_X_dressed_Z (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S 0 s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S 0 s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S s.1 q hs

theorem physical_Y_dressed_Z (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S 0 s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S 0 s _).mpr
  rw [paired_Y_bit]
  exact first_zero_chiX S s.1 q hs

theorem actual_X_dressed_Z (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    (BDL26CSSDaviesLocality.coupling S 2 q .x*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*BDL26CSSDaviesLocality.coupling S 2 q .x)*atom S 0 s=0 :=
  physical_X_dressed_Z S s q hs

theorem actual_Y_dressed_Z (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    (BDL26CSSDaviesLocality.coupling S 2 q .y*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*BDL26CSSDaviesLocality.coupling S 2 q .y)*atom S 0 s=0 :=
  physical_Y_dressed_Z S s q hs

theorem actual_Y_package (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S 2 q .y*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*BDL26CSSDaviesLocality.coupling S 2 q .y)*atom S 0 s=0 :=
  ⟨physical_Y_iXZ S q,actual_Y_dressed_Z S s q hs⟩

end QEC.Coding.BDL26FirstZeroEmptySuffix
