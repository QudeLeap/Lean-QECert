import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.ActualFailureReadout

/-!
# FIRST-zero stability on the actual terminal local-Z-face constructor

Project-derived internal refinement of BDL26 paper.tex3383–3484. The raw face
incidence supplies an actual owner, hence success of the unchanged original
lookup. Both returned corrections, all Q/Z fillings and the entire accumulated
original-history potential are retained. Only FIRST zero is assumed. This
constructor case makes no claim of universal reachability, other constructors,
ALL-component coherence, chiZ, Gibbs, Peierls or lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
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
abbrev Error (S : OddScale) := Word F (C S).Q
abbrev Syndrome (S : OddScale) := Word F (C S).Z
abbrev Potential (S : OddScale) := Word F (C S).X
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev parity (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.parity S

def faceSupported (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S) : Prop :=
  hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
    (C S) (.inl (.inl ⟨z,f⟩))

/-- Every nonzero actual face-star coordinate has the internally derived Z owner. -/
theorem face_owner (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) (r : RZQ (P S) S) (hr : h r≠0) :
    BDL26ReplacementSupport.rzCorrectionOwner (P S) S r=Vertex.z z := by
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp
    (hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩))
  change rzXQIncidence (P S) (rxState S baseState).admissible.toTannerSquareAdmissible S
    (.inl (.inl ⟨z,f⟩)) r=true at hi
  rcases r with ⟨z',edge⟩ | ⟨q,v⟩
  · change decide (∃ hz : z'=z,
      doubleCylinderFaceEdgeMatrix (transposePresentation (P S)) z S
        (hz ▸ edge) f=1)=true at hi
    obtain ⟨hz,_⟩ := of_decide_eq_true hi
    change Vertex.z z'=Vertex.z z
    exact congrArg Vertex.z hz
  · change false=true at hi
    contradiction

/-- Owner locality is a conclusion from raw incidence, not a caller premise. -/
theorem face_local (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : levelTwoLocalError S h := by
  apply (levelTwoLocalError_iff_owner S h).mpr
  exact ⟨Vertex.z z,face_owner S z f h hh⟩

/-- The original full finite table and its original predicate succeed. -/
theorem face_search (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (delta S h) :=
  (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨h,face_local S z f h hh,rfl⟩

/-- The exact returned word is kept; no equality of input and returned owners. -/
theorem face_returned (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (delta S h)=some w ∧
      D S (delta S h)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (delta S h)) ∧ delta S (D S (delta S h))=delta S h := by
  obtain ⟨w,hw⟩ := face_search S z f h hh
  exact ⟨w,hw,BDL26LevelTwoLocalBranchEndpoint.returned_word S _ w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw⟩

/-- Full face coefficients have zero preceding-Q parity. -/
theorem face_parity (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : parity S h=0 :=
  BDL26LevelTwoLocalBranchEndpoint.face_parity_zero S z f h hh

/-- Both actual base outputs are present before legitimate zero normalization. -/
def faceResidual (S : OddScale) (h : Error S) : Error S := h+D S 0+D S (delta S h)

private theorem twice {I : Type} (w : Word F I) : w+w=0 := by
  funext i
  exact ZModModule.add_self (w i)

/-- Transport the complete parity operation before instantiating any word. -/
private theorem q_parity_heq {U V : TannerSquarePresentation} (e : U=V) (S : OddScale) :
    HEq (rzQParity U S) (rzQParity V S) := by
  cases e
  rfl

private theorem levelOne_parity (S : OddScale) :
    (rzQParity (levelOnePresentation S) S : Error S →ₗ[F] Word F (P S).Q)=parity S :=
  eq_of_heq (q_parity_heq
    (show levelOnePresentation S=BDL26LevelTwoLocalBranchEndpoint.P S from rfl) S)

theorem face_residual_closed (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : delta S (faceResidual S h)=0 := by
  obtain ⟨w,hw⟩ := face_search S z f h hh
  have hd : delta S (D S (delta S h))=delta S h :=
    (BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw).2
  have hz : D S (0 : Syndrome S)=0 := BDL26LevelTwoLocalBranchEndpoint.decode_zero S
  change delta S (h+D S 0+D S (delta S h))=0
  rw [hz,add_zero,map_add,hd]
  exact twice _

/-- The complete closed residual, with independently returned owner, has zero parity. -/
theorem face_residual_parity (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : parity S (faceResidual S h)=0 := by
  obtain ⟨w,hw⟩ := face_search S z f h hh
  have hl := (BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw).1
  obtain ⟨a,b,hab⟩ := levelTwoLocalError_add_qParity_two_coordinates S
    (levelOneQDefault S) h (D S (delta S h)) (face_local S z f h hh) hl
  have hc := face_residual_closed S z f h hh
  have hp := rzQParity_cocycle (P S) (rxState S baseState).admissible S (faceResidual S h) hc
  have hz : D S (0 : Syndrome S)=0 := BDL26LevelTwoLocalBranchEndpoint.decode_zero S
  have hr : faceResidual S h=h+D S (delta S h) := by
    change h+D S 0+D S (delta S h)=h+D S (delta S h)
    rw [hz,add_zero]
  apply levelOne_two_support_cocycle_zero S _ hp a b
  intro q hq
  apply hab q
  have hq' : parity S (h+D S (delta S h)) q≠0 := by
    intro hzero
    exact hq ((congrArg (fun r : Error S => parity S r q) hr).trans hzero)
  have hvalue := congrArg (fun op : Error S →ₗ[F] Word F (P S).Q =>
    op (h+D S (delta S h)) q) (levelOne_parity S)
  exact fun hzero => hq' (hvalue.symm.trans hzero)

/-- ALL Q-edge and Z-face filling equations are proved, not supplied by a caller. -/
theorem face_full_filling (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    ∃ pQ pZ : Potential S,
      (∀ q v, boundary S pQ (.inr ⟨q,v⟩)=faceResidual S h (.inr ⟨q,v⟩)) ∧
      (∀ q v, (faceResidual S h+boundary S pQ) (.inr ⟨q,v⟩)=0) ∧
      boundary S pZ=faceResidual S h+boundary S pQ ∧
      boundary S (pZ+pQ)=faceResidual S h :=
  BDL26LevelTwoLocalBranchEndpoint.full_filling S _
    (face_residual_closed S z f h hh) (face_residual_parity S z f h hh)

def faceQPotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  Classical.choose (face_full_filling S z f h hh)

def faceZPotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  Classical.choose (Classical.choose_spec (face_full_filling S z f h hh))

theorem face_fillings_spec (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    (∀ q v, boundary S (faceQPotential S z f h hh) (.inr ⟨q,v⟩)=
      faceResidual S h (.inr ⟨q,v⟩)) ∧
    (∀ q v, (faceResidual S h+boundary S (faceQPotential S z f h hh)) (.inr ⟨q,v⟩)=0) ∧
    boundary S (faceZPotential S z f h hh)=faceResidual S h+boundary S (faceQPotential S z f h hh) ∧
    boundary S (faceZPotential S z f h hh+faceQPotential S z f h hh)=faceResidual S h :=
  Classical.choose_spec (Classical.choose_spec (face_full_filling S z f h hh))

def facePotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  faceZPotential S z f h hh+faceQPotential S z f h hh

theorem face_potential_spec (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    boundary S (facePotential S z f h hh)=h+D S 0+D S (delta S h) :=
  (face_fillings_spec S z f h hh).2.2.2

/-- The branch is an equality on the ALREADY computed terminal centre. -/
def terminalFace (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S) : Prop :=
  (descent S n u q).center=(.inl (.inl ⟨z,f⟩) : (state S 2).presentation.X)

/-- Equality elimination transports whole operations, before fixing any constructor. -/
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

private theorem actual_delta1 (S : OddScale) :
    (tannerCoboundary1 (state S 2).presentation : Error S →ₗ[F] Syndrome S)=delta S :=
  eq_of_heq (presentation_operations_heq (actual_presentation S)).2.2.2

/-- Full actual support is transported to the exact raw face, without a new centre. -/
theorem terminal_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : faceSupported S z f (descent S n u q).word := by
  have hm := presentation_operations_heq (actual_presentation S)
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) :=
    eq_of_heq hm.2.1
  have hh := descent_supported S n u q
  change (fun w : Word F (state S 2).presentation.Q => hammingSupport w)
      (descent S n u q).word ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (descent S n u q).center at hh
  change (descent S n u q).center=(.inl (.inl ⟨z,f⟩) : (C S).X) at hf
  rw [hf] at hh
  have hhs := congrArg (fun support : Error S → Finset (C S).Q =>
    support (descent S n u q).word) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q =>
    star (.inl (.inl ⟨z,f⟩))) hstar
  intro r hr
  have hri := Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
  have hro := hh hri
  exact Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) hro

/-- FIRST zero identifies delta(h) with the unrestricted SECOND original readout. -/
theorem terminal_syndrome (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) :
    delta S (descent S n u q).word=secondReadout S n u q := by
  have hd := descent_syndrome S n u q
  rw [suffix_delta1] at hd
  have he := LinearMap.congr_fun (actual_delta1 S) (descent S n u q).word
  have ht : delta S (descent S n u q).word=
      (firstReadout S n u : Syndrome S)+secondReadout S n u q := he.symm.trans hd
  have hs' : (firstReadout S n u : Syndrome S)=0 := hs
  rw [hs',zero_add] at ht
  exact ht

/-- The second actual original lookup succeeds, even when its input is nonzero. -/
theorem second_search (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S n u q) := by
  rw [← terminal_syndrome S n u q hs]
  exact face_search S z f _ (terminal_supported S n u q z f hf)

/-- Nonzero SECOND readout retains a genuinely nonzero actual correction. -/
theorem second_nonzero_output (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f)
    (ht : secondReadout S n u q≠0) : D S (secondReadout S n u q)≠0 :=
  BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output S _
    (second_search S n u q z f hs hf) ht

/-- Internally fixed full pZ+pQ on the literal actual terminal word. -/
def baseFacePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : (SuffixData S n).family.Cochain0 0 :=
  facePotential S z f (descent S n u q).word (terminal_supported S n u q z f hf)

/-- Both original stored base calls remain in the complete endpoint equation. -/
theorem base_face_potential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    (SuffixData S n).family.coboundary0 0 (baseFacePotential S n u q z f hf)=
      (descent S n u q).word+
        (actualBase S n).decode (actualInputs S n (input S n u) 0)+
        (actualBase S n).decode
          (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0) := by
  have hp := face_potential_spec S z f (descent S n u q).word
    (terminal_supported S n u q z f hf)
  rw [terminal_syndrome S n u q hs] at hp
  have he := LinearMap.congr_fun (actual_delta0 S) (baseFacePotential S n u q z f hf)
  have hfirst : (actualBase S n).decode (actualInputs S n (input S n u) 0)=D S 0 := by
    have hcall : (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        D S (firstReadout S n u) := first_base_original_D S n u
    exact hcall.trans (congrArg (D S) hs)
  have hsecond : (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
        D S (secondReadout S n u q) := second_base_original_D S n u q
  let h : Error S := (descent S n u q).word
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hfilled := hp.trans hcalls
  have hbase : (SuffixData S n).family.coboundary0 0 (baseFacePotential S n u q z f hf)=
      boundary S (baseFacePotential S n u q z f hf) := by
    rw [suffix_delta0]
    exact he
  exact hbase.trans hfilled

/-- Full intervalMap0(pZ+pQ) PLUS the entire original accumulated potential. -/
def fullFacePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (baseFacePotential S n u q z f hf)+accumulated S n u q

/-- No earlier correction or SECOND correction is erased in the top equation. -/
theorem full_face_potential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullFacePotential S n u q z f hf)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold fullFacePotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_face_potential_spec S n u q z f hs hf]
  exact (full_history S n u q).symm

/-- Exact original corrections on the literal realizable input and its translate. -/
theorem original_correction_equation (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullFacePotential S n u q z f hf)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [full_face_potential_spec S n u q z f hs hf]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl

/-- FIRST-zero, actual-terminal-face stability for every scale, parity and depth. -/
theorem first_zero_chiX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨fullFacePotential S n u q z f hf,?_⟩
  rw [full_residual]
  exact full_face_potential_spec S n u q z f hs hf

/-- The empty interval keeps the same physical flip and has no earlier terms. -/
theorem empty_suffix (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S 0 u=0) (hf : terminalFace S 0 u q z f) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 ∧
      BDL26LogicalDefectProtection.chiX S 0 u q=0 :=
  ⟨(BDL26ActualFailureReadout.empty_suffix S u q).1,
    (BDL26ActualFailureReadout.empty_suffix S u q).2,first_zero_chiX S 0 u q z f hs hf⟩

/-- Source-even k1 is included; no large-scale or minimum-weight premise. -/
theorem source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S (2*(k-1)) u=0)
    (hf : terminalFace S (2*(k-1)) u q z f) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,first_zero_chiX S _ u q z f hs hf⟩

/-- Repeated original inputs cancel without an assumption that the input is zero. -/
theorem repeated_input (S : OddScale) (s : Syndrome S) :
    boundary S (0 : Potential S)=(0 : Error S)+D S s+D S s :=
  BDL26LevelTwoLocalBranchEndpoint.repeated_input S s

open QEC.Semantics BDL26PairedDecoderPhase

/-- Direct genuine physical Y=iXZ before any sector compression. -/
theorem physical_Y_iXZ (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) :=
  BDL26ActualFailureReadout.physical_Y_iXZ S n q

theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S n s.1 q z f hs hf

theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_Y_bit]
  exact first_zero_chiX S n s.1 q z f hs hf

theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*
      atom S n s=0 :=
  physical_X_dressed_Z S n s q z f hs hf

theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*
      atom S n s=0 :=
  physical_Y_dressed_Z S n s q z f hs hf

/-- Direct Y identity and actual dressed-Z protection are consumed together. -/
theorem actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*
      atom S n s=0 :=
  ⟨physical_Y_iXZ S n q,actual_Y_dressed_Z S n s q z f hs hf⟩

end QEC.Coding.BDL26FirstZeroFaceEndpoint
