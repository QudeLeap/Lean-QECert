import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDefectProtection
import QEC.Coding.FiniteAlternatingConstruction.HistoryLogicalResidual
import QEC.Coding.FiniteAlternatingConstruction.LocalizedHistoryErrorDescent
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoLocalBranchEndpoint
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoOldXStarEndpoint

/-!
# Actual X failure and two literal original C2 readouts

Project-derived internal refinement of BDL26 paper.tex3383–3484. Both original
histories and their complete corrections are retained. Closed full physical
C2 X-stars are filled, and BOTH zero readouts give an explicit full top
potential. This is not FIRST-zero stability, root activation, a dual chiZ
statement, a witness/minimum-size bound or a thermal lifetime theorem.
-/
noncomputable section
namespace QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators

abbrev F := BDL26Field
abbrev RawOne (S : OddScale) := (rxState S baseState).presentation
abbrev RawTwo (S : OddScale) := (rzState S (rxState S baseState)).presentation

/-- The input inside the ORIGINAL xCorrection, with its genuine range proof. -/
def input (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) : TopInput S n :=
  ⟨u.val,by
    obtain ⟨w,hw⟩ := u.property
    exact ⟨w,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S (n+2) (TopIndex (n+2))) w).trans hw⟩⟩

@[simp] theorem input_value (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    (input S n u).val=u.val := rfl

/-- The entire same original correction, not a new chosen preimage. -/
theorem input_correction (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    historyLiftedCorrection (SuffixData S n) (actualHistory S n (input S n u))=
      xCorrection S n u := rfl

/-- Both translations preserve the same value and hence the same stored input. -/
theorem input_translate (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (e : Word F (Physical S (n+2))) :
    perturbTop S n (input S n u) e=input S n (translateX S n u e) := by
  apply Subtype.ext
  change u.val+(indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e=
    u.val+zSyndrome S (n+2) e
  rw [indexedFamily_coboundary1]
  rfl

abbrev flip (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    Word F (Physical S (n+2)) := Pi.single q 1

theorem flip_eq_basis (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    flip S n q=canonicalBasisWord (F := F) q := by
  funext r
  by_cases h : r=q <;> simp [flip,canonicalBasisWord,h]

/-- Exact full residual, retaining BOTH original histories and C2 corrections. -/
theorem full_residual (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    topWord S n (input S n u) (flip S n q)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold topWord fullCorrection
  rw [input_translate,input_correction,input_correction]
  unfold BDL26LogicalDefectProtection.deltaX flip
  ac_rfl

/-- Actual chiX is the canonical coefficient of the FULL original top word. -/
theorem chiX_top_coefficient (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.chiX S n u q=
      topCoefficient S n (input S n u) (flip S n q) := by
  change _=BDL26LogicalDefectProtection.h1Coordinate S n
    (topCocycle S n (input S n u) (flip S n q))
  rw [BDL26LogicalDefectProtection.h1Coordinate_eq_pairing]
  change _=wordPairing (topWord S n (input S n u) (flip S n q))
    (BDL26LogicalDefectProtection.zWord S n)
  rw [full_residual]
  rfl

/-- The lower coefficient uses the SAME two correlated descents and base words. -/
theorem chiX_lower_coefficient (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : (SuffixData S n).family.Cochain1 (TopIndex n))
    (ha : (SuffixData S n).family.coboundary1 (TopIndex n) a=(input S n u).val) :
    BDL26LogicalDefectProtection.chiX S n u q=
      lowerCoefficient S n (input S n u) (flip S n q) a ha :=
  (chiX_top_coefficient S n u q).trans
    (coefficient_equality S n (input S n u) (flip S n q) a ha)

/-- Zero has a genuine original owner; no caller supplies owner locality. -/
theorem zero_original_local (S : OddScale) :
    levelTwoLocalError S (0 : Word F (levelTwoPresentation S).Q) := by
  apply (levelTwoLocalError_iff_owner S 0).mpr
  refine ⟨Vertex.q (levelOneQDefault S),?_⟩
  intro q hq
  exact False.elim (hq rfl)

/-- Full old-X copy-zero lift and ALL Q-edge/Z-face terms, for EITHER input copy. -/
theorem oldX_closed_full_potential (S : OddScale)
    (x : (levelOnePresentation S).X) (c : BDL26FiniteTannerSquare.Two)
    (h : Word F (levelTwoPresentation S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (levelTwoPresentation S) (Sum.inr (x,c)))
    (hc : tannerCoboundary1 (levelTwoPresentation S) h=0) :
    ∃ (g : Word F (levelOnePresentation S).X)
      (edges : ∀ q : (levelOnePresentation S).Q,
        Word F (QDoubleCylinderEdge (transposePresentation (levelOnePresentation S)) q S))
      (faces : ∀ z : (levelOnePresentation S).Z,
        Word F (ZDoubleCylinderFace (levelOnePresentation S) z S)),
      tannerCoboundary0 (levelTwoPresentation S)
        (BDL26LevelTwoOldXStarEndpoint.oldXLift S g+
          (∑ q,(show Word F (levelTwoPresentation S).X from
            BDL26ReplacementCochainMaps.extendRZQEdgeWord (levelOnePresentation S) S q (edges q)))+
          (∑ z,(show Word F (levelTwoPresentation S).X from
            BDL26ReplacementCochainMaps.extendRZFaceWord (levelOnePresentation S) S z (faces z))))=h := by
  have hz := zero_original_local S
  have ht := BDL26LevelTwoOldXStarEndpoint.oldX_two_local_full_potential
    S x c h 0 0 hh hz hz (by simpa only [add_zero] using hc)
  simpa only [add_zero] using ht

/-- Presentation equality transports the complete operations before any concrete
old-X constructor or word is fixed. Each operation retains its original finite
instances; the result is proved by equality elimination, not supplied by a caller. -/
private theorem presentation_operations_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar U)
      (BDL26RXPhysicalStarTransport.physicalXStar V) ∧
    HEq (fun w : Word F U.Q => hammingSupport w)
      (fun w : Word F V.Q => hammingSupport w) ∧
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) ∧
    HEq (tannerCoboundary1 U) (tannerCoboundary1 V) := by
  cases e
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

private theorem raw_oldX_closed (S : OddScale) :
    ∀ (x : (RawOne S).X) (c : BDL26FiniteTannerSquare.Two) (h : Word F (RawTwo S).Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (RawTwo S) (Sum.inr (x,c)) →
      tannerCoboundary1 (RawTwo S) h=0 →
      ∃ p : Word F (RawTwo S).X, tannerCoboundary0 (RawTwo S) p=h := by
  have ht : ∀ (x : (levelOnePresentation S).X) (c : BDL26FiniteTannerSquare.Two)
      (h : Word F (levelTwoPresentation S).Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (levelTwoPresentation S) (Sum.inr (x,c)) →
      tannerCoboundary1 (levelTwoPresentation S) h=0 →
      ∃ p : Word F (levelTwoPresentation S).X,
        tannerCoboundary0 (levelTwoPresentation S) p=h := by
    intro x c h hh hc
    obtain ⟨g,edges,faces,hp⟩ := oldX_closed_full_potential S x c h hh hc
    exact ⟨_,hp⟩
  have he : levelTwoPresentation S=RawTwo S :=
    congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
  have hm := presentation_operations_heq he
  -- All four equalities now live on the SAME literal closed coordinate types.
  -- No equality motive contains a concrete Sum.inr old-X constructor.
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (levelTwoPresentation S) :
      (RawTwo S).X → Finset (RawTwo S).Q)=
      BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) := eq_of_heq hm.1
  have hsupport : ((fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) :
      Word F (RawTwo S).Q → Finset (RawTwo S).Q)=
      (fun w : Word F (RawTwo S).Q => hammingSupport w) := eq_of_heq hm.2.1
  have hdelta0 : (tannerCoboundary0 (levelTwoPresentation S) :
      Word F (RawTwo S).X →ₗ[F] Word F (RawTwo S).Q)=
      tannerCoboundary0 (RawTwo S) := eq_of_heq hm.2.2.1
  have hdelta1 : (tannerCoboundary1 (levelTwoPresentation S) :
      Word F (RawTwo S).Q →ₗ[F] Word F (RawTwo S).Z)=
      tannerCoboundary1 (RawTwo S) := eq_of_heq hm.2.2.2
  intro x c h hh hc
  have hhs : (fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) h=
      hammingSupport h :=
    congrArg (fun support : Word F (RawTwo S).Q → Finset (RawTwo S).Q => support h) hsupport
  have hxs : BDL26RXPhysicalStarTransport.physicalXStar
      (levelTwoPresentation S) (Sum.inr (x,c))=
      BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) (Sum.inr (x,c)) :=
    congrArg (fun star : (RawTwo S).X → Finset (RawTwo S).Q => star (Sum.inr (x,c))) hstar
  have hh' : (fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) h ⊆
      BDL26RXPhysicalStarTransport.physicalXStar
        (levelTwoPresentation S) (Sum.inr (x,c)) := by
    rw [hhs,hxs]
    exact hh
  have hc' : tannerCoboundary1 (levelTwoPresentation S) h=0 :=
    (LinearMap.congr_fun hdelta1 h).trans hc
  obtain ⟨p,hp⟩ := ht x c h hh' hc'
  exact ⟨p,(LinearMap.congr_fun hdelta0 p).symm.trans hp⟩

/-- All coefficients in a local Z face are filled using the actual zero branch. -/
theorem face_closed_boundary (S : OddScale) (z : (RawOne S).Z)
    (f : ZDoubleCylinderFace (RawOne S) z S) (h : Word F (RawTwo S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (RawTwo S) (.inl (.inl ⟨z,f⟩)))
    (hc : tannerCoboundary1 (RawTwo S) h=0) :
    ∃ p : Word F (RawTwo S).X, tannerCoboundary0 (RawTwo S) p=h := by
  have hs : BDL26LevelTwoLocalBranchEndpoint.localSuccess S
      (BDL26LevelTwoLocalBranchEndpoint.delta S h) := by
    rw [show BDL26LevelTwoLocalBranchEndpoint.delta S h=0 from hc]
    exact BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  obtain ⟨p,hp⟩ := BDL26LevelTwoLocalBranchEndpoint.face_endpoint S z f h hh hs
  refine ⟨p,?_⟩
  change tannerCoboundary0 (RawTwo S) p=
    h+BDL26LevelTwoLocalBranchEndpoint.D S 0+
      BDL26LevelTwoLocalBranchEndpoint.D S (tannerCoboundary1 (RawTwo S) h) at hp
  simpa only [hc,BDL26LevelTwoLocalBranchEndpoint.decode_zero,add_zero] using hp

/-- Full Q-edge star, not a support<=2 or weight-to-owner assertion. -/
theorem edge_closed_boundary (S : OddScale) (q : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) q S)
    (h : Word F (RawTwo S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (RawTwo S) (.inl (.inr ⟨q,e⟩)))
    (hc : tannerCoboundary1 (RawTwo S) h=0) :
    ∃ p : Word F (RawTwo S).X, tannerCoboundary0 (RawTwo S) p=h := by
  have hs : BDL26LevelTwoLocalBranchEndpoint.localSuccess S
      (BDL26LevelTwoLocalBranchEndpoint.delta S h) := by
    rw [show BDL26LevelTwoLocalBranchEndpoint.delta S h=0 from hc]
    exact BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  obtain ⟨p,hp⟩ := BDL26LevelTwoLocalBranchEndpoint.edge_endpoint S q e h hh hs
  refine ⟨p,?_⟩
  change tannerCoboundary0 (RawTwo S) p=
    h+BDL26LevelTwoLocalBranchEndpoint.D S 0+
      BDL26LevelTwoLocalBranchEndpoint.D S (tannerCoboundary1 (RawTwo S) h) at hp
  simpa only [hc,BDL26LevelTwoLocalBranchEndpoint.decode_zero,add_zero] using hp

private theorem raw_closed_star (S : OddScale) :
    ∀ (x : (RawTwo S).X) (h : Word F (RawTwo S).Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) x →
      tannerCoboundary1 (RawTwo S) h=0 →
      ∃ p : Word F (RawTwo S).X, tannerCoboundary0 (RawTwo S) p=h := by
  intro x h hh hc
  change RZX (RawOne S) S at x
  rcases x with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · exact face_closed_boundary S z f h hh hc
  · exact edge_closed_boundary S q e h hh hc
  · exact raw_oldX_closed S x c h hh hc

/-- Exhaustive actual C2 star filling, all S including half1 and both old-X copies. -/
theorem closed_C2_star_boundary (S : OddScale) :
    ∀ (x : (state S 2).presentation.X) (h : Word F (state S 2).presentation.Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation x →
      tannerCoboundary1 (state S 2).presentation h=0 →
      ∃ p : Word F (state S 2).presentation.X,
        tannerCoboundary0 (state S 2).presentation p=h := by
  have hp : (state S 2).presentation=RawTwo S :=
    congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
  rw [hp]
  exact raw_closed_star S

/-- Literal original C2 readout values, not a history at the residual syndrome0. -/
def firstReadout (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :=
  (actualInputs S n (input S n u) 0).val

def secondReadout (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :=
  (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0).val

theorem firstReadout_stored (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    firstReadout S n u=(BDL26CanonicalHistoryMarks.inputAt S n (input S n u) 0).val := by
  rw [BDL26RZPhysicalXStarTransport.original_input_eq]
  rfl

theorem secondReadout_stored (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    secondReadout S n u q=(BDL26CanonicalHistoryMarks.inputAt S n
      (input S n (translateX S n u (flip S n q))) 0).val := by
  rw [BDL26RZPhysicalXStarTransport.original_input_eq,← input_translate]
  rfl

theorem firstReadout_marks_base (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    firstReadout S n u=(BDL26CanonicalHistoryMarks.baseInput S n (input S n u)).val :=
  firstReadout_stored S n u

theorem secondReadout_marks_base (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    secondReadout S n u q=(BDL26CanonicalHistoryMarks.baseInput S n
      (input S n (translateX S n u (flip S n q)))).val :=
  secondReadout_stored S n u q

theorem firstReadout_original (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    firstReadout S n u=actualReadout S n (input S n u) 0 :=
  (actualInputs_readout S n (input S n u) 0).symm

theorem secondReadout_original (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    secondReadout S n u q=actualReadout S n (input S n (translateX S n u (flip S n q))) 0 := by
  rw [actualInputs_readout,← input_translate]
  rfl

/-- The stored base calls use the unchanged executable decoder D on both values. -/
theorem first_base_original_D (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    (actualBase S n).decode (actualInputs S n (input S n u) 0)=
      BDL26LevelTwoDecoder.decode S (firstReadout S n u) := rfl

theorem second_base_original_D (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
      BDL26LevelTwoDecoder.decode S (secondReadout S n u q) := rfl

private theorem first_base_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (hs : firstReadout S n u=0) :
    (actualBase S n).decode (actualInputs S n (input S n u) 0)=0 := by
  have hi : actualInputs S n (input S n u) 0=0 := Subtype.ext hs
  rw [hi,actualBase_decode_zero]

private theorem second_base_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (ht : secondReadout S n u q=0) :
    (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=0 := by
  have hi : actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0=0 :=
    Subtype.ext ht
  rw [hi,actualBase_decode_zero]

private theorem flip_supported (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    hammingSupport (flip S n q) ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n)
      (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact BDL26LocalizedHistoryErrorDescent.elementary_support S n q

/-- The actual internally correlated localized descent of this physical flip. -/
def descent (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2)) :=
  BDL26LocalizedHistoryErrorDescent.actualDescent S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q) 0

/-- ALL original accumulated degree-zero terms, with no truncation or zero assumption. -/
def accumulated (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2)) :=
  BDL26LocalizedHistoryErrorDescent.actualPotential S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q) 0 (TopIndex n)

theorem descent_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    hammingSupport (descent S n u q).word ⊆
      BDL26LocalizedHistoryErrorDescent.star S n 0 (descent S n u q).center :=
  BDL26LocalizedHistoryErrorDescent.actualDescent_supported S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q) 0

theorem descent_syndrome (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    (SuffixData S n).family.coboundary1 0 (descent S n u q).word=
      firstReadout S n u+secondReadout S n u q :=
  BDL26LocalizedHistoryErrorDescent.actualDescent_syndrome S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q) 0

/-- Complete two-history equation before either C2 word is proved zero. -/
theorem full_history (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.deltaX S n u q=
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        ((descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0))+
      (SuffixData S n).family.coboundary0 (TopIndex n) (accumulated S n u q) := by
  have h := BDL26LocalizedHistoryErrorDescent.actual_history S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q)
  change topWord S n (input S n u) (flip S n q)=_ at h
  rw [full_residual] at h
  exact h

private theorem base_boundary_exists (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    ∃ p : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 p=(descent S n u q).word := by
  have hc := descent_syndrome S n u q
  rw [hs,ht,add_zero] at hc
  rw [suffix_delta1] at hc
  obtain ⟨p,hp⟩ := closed_C2_star_boundary S (descent S n u q).center
    (descent S n u q).word (descent_supported S n u q) hc
  refine ⟨p,?_⟩
  rw [suffix_delta0]
  exact hp

/-- Chosen only from the proved exhaustive filling; no caller supplies a boundary. -/
def basePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    (SuffixData S n).family.Cochain0 0 :=
  Classical.choose (base_boundary_exists S n u q hs ht)

theorem basePotential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    (SuffixData S n).family.coboundary0 0 (basePotential S n u q hs ht)=(descent S n u q).word :=
  Classical.choose_spec (base_boundary_exists S n u q hs ht)

/-- Literal full intervalMap0 p2 plus literal entire original accumulated potential. -/
def topPotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (basePotential S n u q hs ht)+
    accumulated S n u q

/-- The full top potential is proved with the generic degree-zero cochain equation. -/
theorem topPotential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (topPotential S n u q hs ht)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold topPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),basePotential_spec]
  have h := full_history S n u q
  rw [first_base_zero S n u hs,second_base_zero S n u q ht,add_zero,add_zero] at h
  exact h.symm

/-- BOTH literal zero readouts force the actual X logical bit to vanish. -/
theorem chiX_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨topPotential S n u q hs ht,?_⟩
  rw [full_residual]
  exact topPotential_spec S n u q hs ht

/-- Necessary TWO-history readout alternative, without choosing the first history. -/
theorem chiX_one_readout (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    firstReadout S n u≠0 ∨ secondReadout S n u q≠0 := by
  by_cases hs : firstReadout S n u=0
  · by_cases ht : secondReadout S n u q=0
    · exact False.elim (one_ne_zero (hc.symm.trans (chiX_zero S n u q hs ht)))
    · exact Or.inr ht
  · exact Or.inl hs

/-- Empty suffix has the original physical word and no earlier potential terms. -/
theorem empty_suffix (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 :=
  BDL26LocalizedHistoryErrorDescent.depth_two S (input S 0 u) (flip S 0 q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S 0 q) (flip_supported S 0 q)

/-- Every source-even k>=1, including k1, with no strict scale restriction. -/
theorem source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hs : firstReadout S (2*(k-1)) u=0) (ht : secondReadout S (2*(k-1)) u q=0) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,chiX_zero S _ u q hs ht⟩

open QEC.Semantics BDL26PairedDecoderPhase

/-- The X bit of the actual paired physical X residual is the same chiX. -/
theorem paired_X_bit (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=
      BDL26LogicalDefectProtection.chiX S n s.1 q := by
  unfold BDL26LogicalDefectProtection.dX
  rw [(BDL26LogicalDefectProtection.residual_single_x S n s q).1]
  rfl

/-- SAME actual Y residual's X bit; no claim about its independent Z bit. -/
theorem paired_Y_bit (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=
      BDL26LogicalDefectProtection.chiX S n s.1 q := by
  unfold BDL26LogicalDefectProtection.dX
  rw [(BDL26LogicalDefectProtection.residual_single_y S n s q).1]
  rfl

/-- Full actual atom commutator for physical X and the dressed Z observable. -/
theorem physical_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0) (ht : secondReadout S n s.1 q=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_X_bit]
  exact chiX_zero S n s.1 q hs ht

/-- Full physical Y consumer; it is not a product of compressed commutators. -/
theorem physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0) (ht : secondReadout S n s.1 q=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_Y_bit]
  exact chiX_zero S n s.1 q hs ht

/-- Direct actual physical-Y identity retained in the same universal package. -/
theorem physical_Y_iXZ (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I •
      (Qubit.localX q*Qubit.localZ q) := actual_Y_operator S n q

/-- The literal actual recursive coupling, rather than a changed observable. -/
theorem actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0) (ht : secondReadout S n s.1 q=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*
      atom S n s=0 :=
  physical_X_dressed_Z S n s q hs ht

/-- Physical Y is used before compression, with the same two original readouts. -/
theorem actual_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0) (ht : secondReadout S n s.1 q=0) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*
      atom S n s=0 :=
  physical_Y_dressed_Z S n s q hs ht

end QEC.Coding.BDL26ActualFailureReadout
