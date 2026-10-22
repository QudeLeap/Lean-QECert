import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoderZero
import QEC.Coding.FiniteAlternatingConstruction.RZPhysicalXStarTransport

/-!
# Full physical C2 endpoints on the original local-search branch

Internal source-derived refinement of BDL26 paper.tex3404–3484. The table,
order, predicate, physical coordinates and full original corrections are fixed.
The result is conditional on the ACTUAL first search, not on a chosen local
representative. It does not establish the remaining reachable fallback or
old-X cases of the stable-syndrome criterion.
-/
noncomputable section
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators

abbrev Bit := BDL26FiniteTannerSquare.Field
abbrev P (S : OddScale) := (rxState S baseState).presentation
abbrev C (S : OddScale) := (rzState S (rxState S baseState)).presentation
abbrev A (S : OddScale) : TannerSquareAdmissibleV4 (P S) :=
  (rxState S baseState).admissible
abbrev Error (S : OddScale) := Word Bit (C S).Q
abbrev Syndrome (S : OddScale) := Word Bit (C S).Z
abbrev Potential (S : OddScale) := Word Bit (C S).X
abbrev D (S : OddScale) : Syndrome S → Error S := BDL26LevelTwoDecoder.decode S
abbrev delta (S : OddScale) : Error S →ₗ[Bit] Syndrome S := tannerCoboundary1 (C S)
abbrev boundary (S : OddScale) : Potential S →ₗ[Bit] Error S := tannerCoboundary0 (C S)
abbrev parity (S : OddScale) := rzQParity (P S) S

/-- Exactly the ORIGINAL first table search; no sorting/filter changes. -/
def localSearch (S : OddScale) (t : Syndrome S) :
    Option (Word Bit (BDL26LevelTwoDecoder.ExecutableQ S)) :=
  BDL26LevelTwoDecoder.search
    (fun w => BDL26LevelTwoDecoder.executableLocal S w &&
      decide (BDL26LevelTwoDecoder.executableSyndrome S w=
        BDL26LevelTwoDecoder.toExecutableSyndrome S t))
    (BDL26LevelTwoDecoder.allWords (BDL26LevelTwoDecoder.ExecutableQ S))

/-- The separate unfiltered search used ONLY after the first returned none. -/
def globalSearch (S : OddScale) (t : Syndrome S) :
    Option (Word Bit (BDL26LevelTwoDecoder.ExecutableQ S)) :=
  BDL26LevelTwoDecoder.search
    (fun w => decide (BDL26LevelTwoDecoder.executableSyndrome S w=
      BDL26LevelTwoDecoder.toExecutableSyndrome S t))
    (BDL26LevelTwoDecoder.allWords (BDL26LevelTwoDecoder.ExecutableQ S))

/-- This is an actual returned branch, not a redefinition by attainability. -/
def localSuccess (S : OddScale) (t : Syndrome S) : Prop :=
  ∃ w, localSearch S t=some w

open scoped Classical

private theorem actual_presentation (S : OddScale) :
    levelTwoPresentation S=C S :=
  congrArg ConstructionState.presentation (levelTwoState_eq_pair S)

private theorem coboundary1_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (tannerCoboundary1 U) (tannerCoboundary1 V) := by
  cases h
  rfl

private theorem actual_delta (S : OddScale) :
    (tannerCoboundary1 (levelTwoPresentation S) : Error S →ₗ[Bit] Syndrome S)=delta S := by
  exact eq_of_heq (coboundary1_heq (actual_presentation S))

private theorem encoded_delta (S : OddScale) (e : Error S) :
    BDL26LevelTwoDecoder.executableSyndrome S (BDL26LevelTwoDecoder.toExecutableError S e)=
      BDL26LevelTwoDecoder.toExecutableSyndrome S (delta S e) := by
  have he := congrArg (fun F : Error S →ₗ[Bit] Syndrome S => F e) (actual_delta S)
  exact (BDL26LevelTwoDecoder.executableSyndrome_eq S e).trans
    (congrArg (BDL26LevelTwoDecoder.toExecutableSyndrome S) he)

private theorem raw_owner_iff (S : OddScale) (e : Error S) :
    levelTwoLocalError S e ↔ ∃ owner : Vertex (P S), ∀ q : RZQ (P S) S,
      e q≠0 → BDL26ReplacementSupport.rzCorrectionOwner (P S) S q=owner := by
  exact levelTwoLocalError_iff_owner S e

private theorem twice {I : Type} (w : Word Bit I) : w+w=0 := by
  funext i
  exact ZModModule.add_self (w i)

private theorem sum_two_support {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bit) (a b : I) (hab : a≠b)
    (hs : ∀ v, f v≠0 → v=a ∨ v=b) : ∑ v, f v=f a+f b := by
  calc
    _ = ∑ v ∈ ({a,b} : Finset I), f v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      by_contra hn
      exact hv (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hs v hn)
    _ = _ := by
      have hnot : a ∉ ({b} : Finset I) := by simpa only [Finset.mem_singleton] using hab
      rw [Finset.sum_insert hnot,Finset.sum_singleton]

private theorem parity_add (S : OddScale) (first second : Error S) :
    parity S (first+second)=parity S first+parity S second := by
  exact (rzQParity (P S) S).map_add first second

/-- The complete returned executable word is exactly the original correction. -/
theorem returned_word (S : OddScale) (t : Syndrome S)
    (w : Word Bit (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    D S t=BDL26LevelTwoDecoder.toActualError S w := by
  unfold localSearch at hw
  unfold D BDL26LevelTwoDecoder.decode BDL26LevelTwoDecoder.executableDecode
    BDL26LevelTwoDecoder.lookup
  rw [hw]

/-- Locality and syndrome are BOTH derived from the actual returned predicate. -/
theorem returned_local_and_syndrome (S : OddScale) (t : Syndrome S)
    (w : Word Bit (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    levelTwoLocalError S (D S t) ∧ delta S (D S t)=t := by
  have hp := (BDL26LevelTwoDecoder.search_sound _ _ _ hw).2
  have hl := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hp).1
  have hs := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hp).2
  rw [returned_word S t w hw]
  constructor
  · apply (BDL26LevelTwoDecoder.executableLocal_iff S _).1
    simpa only [BDL26LevelTwoDecoder.toExecutableError_toActualError] using hl
  · apply BDL26LevelTwoDecoder.toExecutableSyndrome_injective S
    have h := encoded_delta S (BDL26LevelTwoDecoder.toActualError S w)
    have he : BDL26LevelTwoDecoder.toExecutableError S
        (BDL26LevelTwoDecoder.toActualError S w)=w :=
      BDL26LevelTwoDecoder.toExecutableError_toActualError S w
    have h' : BDL26LevelTwoDecoder.executableSyndrome S w=
        BDL26LevelTwoDecoder.toExecutableSyndrome S
          (delta S (BDL26LevelTwoDecoder.toActualError S w)) :=
      (congrArg (BDL26LevelTwoDecoder.executableSyndrome S) he).symm.trans h
    exact h'.symm.trans (of_decide_eq_true hs)

/-- Exact soundness/completeness on ALL raw physical syndrome words. -/
theorem localSuccess_iff (S : OddScale) (t : Syndrome S) :
    localSuccess S t ↔ ∃ e : Error S, levelTwoLocalError S e ∧ delta S e=t := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨D S t,returned_local_and_syndrome S t w hw⟩
  · rintro ⟨e,he,ht⟩
    unfold localSuccess localSearch
    apply BDL26LevelTwoDecoder.search_complete
    refine ⟨BDL26LevelTwoDecoder.toExecutableError S e,
      BDL26LevelTwoDecoder.mem_allWords _ _,?_⟩
    have hl := (BDL26LevelTwoDecoder.executableLocal_iff S e).2 he
    have hs := (encoded_delta S e).trans
      (congrArg (BDL26LevelTwoDecoder.toExecutableSyndrome S) ht)
    simp only [hl,hs,decide_true,Bool.true_and]

/-- The Boolean view refers to the very same first Option-valued search. -/
theorem localSuccess_isSome (S : OddScale) (t : Syndrome S) :
    localSuccess S t ↔ (localSearch S t).isSome=true := by
  unfold localSuccess
  cases hs : localSearch S t <;> simp

/-- None excludes exactly the original owner-local preimages, not logical errors. -/
theorem localSearch_none_iff (S : OddScale) (t : Syndrome S) :
    localSearch S t=none ↔ ¬∃ e : Error S, levelTwoLocalError S e ∧ delta S e=t := by
  rw [← localSuccess_iff S t]
  unfold localSuccess
  cases hs : localSearch S t <;> simp

/-- A failed first search takes the actual unfiltered branch with its default. -/
theorem fallback_word (S : OddScale) (t : Syndrome S) (hn : localSearch S t=none) :
    D S t=BDL26LevelTwoDecoder.toActualError S ((globalSearch S t).getD 0) := by
  unfold localSearch at hn
  unfold D BDL26LevelTwoDecoder.decode BDL26LevelTwoDecoder.executableDecode
    BDL26LevelTwoDecoder.lookup globalSearch
  rw [hn]

/-- Actual represented syndromes never use the final default, even after none. -/
theorem represented_global_success (S : OddScale) (t : Syndrome S)
    (ht : ∃ e : Error S, delta S e=t) : ∃ w, globalSearch S t=some w := by
  obtain ⟨e,he⟩ := ht
  apply BDL26LevelTwoDecoder.search_complete
  refine ⟨BDL26LevelTwoDecoder.toExecutableError S e,
    BDL26LevelTwoDecoder.mem_allWords _ _,?_⟩
  apply decide_eq_true
  exact (encoded_delta S e).trans
    (congrArg (BDL26LevelTwoDecoder.toExecutableSyndrome S) he)

/-- Physical C2 zero normalization is derived; no earlier correction is changed. -/
theorem decode_zero (S : OddScale) : D S 0=0 :=
  BDL26LevelTwoDecoder.decode_zero S

/-- The actual full X-incidence star, on the literal C2 coordinates. -/
def star (S : OddScale) (u : RZX (P S) S) : Finset (RZQ (P S) S) :=
  BDL26RXPhysicalStarTransport.physicalXStar (C S) u

def supported (S : OddScale) (u : RZX (P S) S) (h : Error S) : Prop :=
  hammingSupport h ⊆ star S u

private theorem supported_incidence (S : OddScale) (u : RZX (P S) S) (h : Error S)
    (hh : supported S u h) (r : RZQ (P S) S) (hr : h r≠0) :
    rzXQIncidence (P S) (A S).toTannerSquareAdmissible S u r=true := by
  have hm := hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
  exact (Finset.mem_filter.mp hm).2

private theorem supported_Q_labels (S : OddScale) (u : RZX (P S) S) (h : Error S)
    (hh : supported S u h) (q : (P S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (P S)) q S) (hv : h (.inr ⟨q,v⟩)≠0) :
    q ∈ BDL26RZPhysicalXStarTransport.rawQ0 (P S) S u := by
  have hs := BDL26RZPhysicalXStarTransport.raw_star_cover (P S)
    (A S).toTannerSquareAdmissible S u (.inr ⟨q,v⟩)
    (supported_incidence S u h hh _ hv)
  exact (BDL26RZFiniteBlockTransport.Coordinates.mem_input_q _ _ _ _ _ _).1 hs

/-- Complete Z-face star words have zero preceding-Q parity, with all Z bits kept. -/
theorem face_parity_zero (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) : parity S h=0 := by
  funext q
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) q S,
    h (.inr ⟨q,v⟩))=0
  apply Finset.sum_eq_zero
  intro v _
  by_contra hv
  have hm := supported_Q_labels S _ h hh q v hv
  change q ∈ (∅ : Finset (P S).Q) at hm
  exact Finset.notMem_empty q hm

/-- No Q label other than the actual Q-edge's own label occurs. -/
theorem edge_parity_other (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) (r : (P S).Q) (hr : r≠q) :
    parity S h r=0 := by
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) r S,
    h (.inr ⟨r,v⟩))=0
  apply Finset.sum_eq_zero
  intro v _
  by_contra hv
  have hm := supported_Q_labels S _ h hh r v hv
  have heq : r=q := by simpa only [BDL26RZPhysicalXStarTransport.rawQ0,
    Finset.mem_singleton] using hm
  exact hr heq

/-- Actual old-X copies retain the FULL preceding incidence-star support. -/
theorem oldX_parity_support (S : OddScale) (x : (P S).X) (copy : BDL26FiniteTannerSquare.Two)
    (h : Error S) (hh : supported S (.inr (x,copy)) h) (q : (P S).Q)
    (hq : parity S h q≠0) :
    q ∈ BDL26RXPhysicalStarTransport.physicalXStar (P S) x := by
  by_contra hn
  apply hq
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) q S,
    h (.inr ⟨q,v⟩))=0
  apply Finset.sum_eq_zero
  intro v _
  by_contra hv
  exact hn (supported_Q_labels S _ h hh q v hv)

/-- Proved locally from tagged actual vertices, including half=1. -/
theorem edge_endpoints_distinct (S : OddScale) (q : (P S).Q)
    (edge : QDoubleCylinderEdge (transposePresentation (P S)) q S) :
    qDoubleCylinderEdgeStart (transposePresentation (P S)) q S edge ≠
      qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S edge := by
  rcases edge with ⟨copy,edge,segment⟩ | endpoint
  · simp [qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,
      qSubdivisionEdgeStart,qSubdivisionEdgeEnd]
    by_cases hstart : segment.1=0
    · by_cases hend : segment.1+1=S.half
      · have hhalf : S.half=1 := by omega
        have hsegment : segment=⟨0,S.half_pos⟩ := Fin.ext (by simpa using hstart)
        subst segment
        simp [hhalf,qStarEdgeStart,qStarEdgeEnd]
      · have hhalf : S.half≠1 := by omega
        have hone : (1 : Nat)≠S.half := Ne.symm hhalf
        simp [hstart,hone,qStarEdgeStart]
    · by_cases hend : segment.1+1=S.half
      · simp [hstart,hend]
      · simp [hstart,hend,Fin.ext_iff]
        omega
  · simp [qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd]

/-- The only possible Q coefficients are the two actual edge endpoints. -/
theorem edge_Q_nonzero (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h)
    (v : QDoubleCylinderVertex (transposePresentation (P S)) q S)
    (hv : h (.inr ⟨q,v⟩)≠0) :
    v=qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e ∨
      v=qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e := by
  have hi := supported_incidence S _ h hh (.inr ⟨q,v⟩) hv
  change decide (∃ heq : q=q,
    heq ▸ v=qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e ∨
    heq ▸ v=qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e)=true at hi
  obtain ⟨heq,hv⟩ := of_decide_eq_true hi
  have hproof : heq=rfl := Subsingleton.elim _ _
  rw [hproof] at hv
  exact hv

/-- Exact coefficient, without assuming equal endpoints or uniform neighbour bits. -/
theorem edge_parity_self (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) :
    parity S h q=
      h (.inr ⟨q,qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e⟩)+
      h (.inr ⟨q,qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e⟩) := by
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) q S,
    h (.inr ⟨q,v⟩))=_
  exact sum_two_support
    (fun v : QDoubleCylinderVertex (transposePresentation (P S)) q S => h (.inr ⟨q,v⟩))
    (qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e)
    (qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e)
    (edge_endpoints_distinct S q e) (edge_Q_nonzero S q e h hh)

private theorem parity_local_label (S : OddScale) (c : Error S)
    (hc : levelTwoLocalError S c) (default : (P S).Q) :
    ∃ a : (P S).Q, ∀ q, q≠a → parity S c q=0 := by
  obtain ⟨owner,ho⟩ := (raw_owner_iff S c).1 hc
  refine ⟨qCoordinateOfOwner (P S) default owner,?_⟩
  intro q hq
  apply rzQParity_zero_of_other_owner (P S) S c owner ho q
  intro heq
  exact hq (qCoordinateOfOwner_of_eq (P S) default q owner heq)

private theorem raw_full_filling (P0 : TannerSquarePresentation)
    (A0 : TannerSquareAdmissibleV4 P0) (R0 : TannerSquareCellularRegular P0) (S : OddScale)
    (r : Word Bit (RZQ P0 S))
    (hc : rzCoboundary1 P0 A0 S r=0) (hp : rzQParity P0 S r=0) :
    ∃ pQ pZ : Word Bit (RZX P0 S),
      (∀ q v, rzCoboundary0 P0 A0 S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩)) ∧
      (∀ q v, (r+rzCoboundary0 P0 A0 S pQ) (.inr ⟨q,v⟩)=0) ∧
      rzCoboundary0 P0 A0 S pZ=r+rzCoboundary0 P0 A0 S pQ ∧
      rzCoboundary0 P0 A0 S (pZ+pQ)=r := by
  obtain ⟨edges,hedges⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings P0 A0.toTannerSquareAdmissible S r hp)
  let pQ : Word Bit (RZX P0 S) := ∑ q : P0.Q, extendRZQEdgeWord P0 S q (edges q)
  have hqp : ∀ q v, rzCoboundary0 P0 A0 S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩) := by
    intro q v
    dsimp only [pQ]
    rw [map_sum,Finset.sum_apply]
    simp only [rzQEdge_coboundary_apply_q,hedges]
    simpa only [Finset.sum_apply] using sum_extendRZQVertexWord_apply P0 S r q v
  let rem : Word Bit (RZQ P0 S) := r+rzCoboundary0 P0 A0 S pQ
  have hq : ∀ q v, rem (.inr ⟨q,v⟩)=0 := by
    intro q v
    change r _+rzCoboundary0 P0 A0 S pQ _=0
    rw [hqp]
    exact ZModModule.add_self _
  have hrem : rzCoboundary1 P0 A0 S rem=0 := by
    dsimp only [rem]
    rw [map_add,hc,zero_add]
    exact LinearMap.congr_fun (tannerCoboundary_squared (rzReplacementPresentation P0 A0.toTannerSquareAdmissible S)) pQ
  have hf : ∀ z : P0.Z, ∃ faces : Word Bit (ZDoubleCylinderFace P0 z S),
      doubleCylinderBoundary2 (transposePresentation P0) z S faces=
        fun e => rem (.inl ⟨z,e⟩) := by
    intro z
    exact zCylinder_cycle_has_filling P0 A0.toTannerSquareAdmissibleV3
      R0 z S _
      (rzLocal_cycle_of_cocycle_q_zero P0 A0 S rem hrem hq z)
  choose faces hfaces using hf
  let pZ : Word Bit (RZX P0 S) := ∑ z : P0.Z, extendRZFaceWord P0 S z (faces z)
  have hz : rzCoboundary0 P0 A0 S pZ=rem := by
    dsimp only [pZ]
    rw [map_sum]
    simp only [rzCoboundary0_extendRZFaceWord,extendRZLocalEdgeWord_eq,hfaces]
    exact (rzWord_eq_sum_local_of_q_zero P0 S rem hq).symm
  refine ⟨pQ,pZ,hqp,hq,hz,?_⟩
  calc
    rzCoboundary0 P0 A0 S (pZ+pQ)=rzCoboundary0 P0 A0 S pZ+rzCoboundary0 P0 A0 S pQ := (rzCoboundary0 P0 A0 S).map_add pZ pQ
    _ = (r+rzCoboundary0 P0 A0 S pQ)+rzCoboundary0 P0 A0 S pQ := by rw [hz]
    _ = r := by rw [add_assoc,twice,add_zero]

/-- Complete fillings on ALL Q cylinders and ALL Z cylinders; no filling input. -/
theorem full_filling (S : OddScale) (r : Error S)
    (hc : delta S r=0) (hp : parity S r=0) :
    ∃ pQ pZ : Potential S,
      (∀ q v, boundary S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩)) ∧
      (∀ q v, (r+boundary S pQ) (.inr ⟨q,v⟩)=0) ∧
      boundary S pZ=r+boundary S pQ ∧ boundary S (pZ+pQ)=r := by
  exact raw_full_filling (P S) (A S) (rxState S baseState).regular S r hc hp

private theorem two_parity_endpoint (S : OddScale) (r : Error S)
    (hc : delta S r=0) (a b : (P S).Q)
    (hs : ∀ q, parity S r q≠0 → q=a ∨ q=b) :
    ∃ p : Potential S, boundary S p=r := by
  have hproj := rzQParity_cocycle (P S) (A S) S r hc
  have hp := levelOne_two_support_cocycle_zero S (parity S r) hproj a b hs
  obtain ⟨pQ,pZ,_,_,_,hpz⟩ := full_filling S r hc hp
  exact ⟨pZ+pQ,hpz⟩

/-- Full one-parity endpoint; h need not be an owner-local error. -/
theorem one_parity_endpoint (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by
  obtain ⟨w,hw⟩ := hb
  obtain ⟨hc,hs⟩ := returned_local_and_syndrome S (delta S h) w hw
  obtain ⟨b,hb⟩ := parity_local_label S (D S (delta S h)) hc a
  have hcycle : delta S (h+D S (delta S h))=0 := by
    rw [map_add,hs]
    exact twice _
  have hsupp : ∀ q, parity S (h+D S (delta S h)) q≠0 → q=a ∨ q=b := by
    intro q hq
    by_contra hn
    have hqa : q≠a := fun heq => hn (Or.inl heq)
    have hqb : q≠b := fun heq => hn (Or.inr heq)
    apply hq
    calc
      parity S (h+D S (delta S h)) q=
          parity S h q+parity S (D S (delta S h)) q :=
        congrFun (parity_add S h (D S (delta S h))) q
      _ = 0 := by rw [ha q hqa,hb q hqb,zero_add]
  obtain ⟨p,hp⟩ := two_parity_endpoint S (h+D S (delta S h)) hcycle a b hsupp
  refine ⟨p,?_⟩
  simpa only [decode_zero,add_zero] using hp

/-- A fixed potential is internally chosen from the derived full construction. -/
def endpointPotential (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) : Potential S :=
  Classical.choose (one_parity_endpoint S h a ha hb)

theorem endpointPotential_spec (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) :
    boundary S (endpointPotential S h a ha hb)=h+D S 0+D S (delta S h) :=
  Classical.choose_spec (one_parity_endpoint S h a ha hb)

/-- All coefficients in the actual Z-face star are retained. -/
theorem face_endpoint (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by
  apply one_parity_endpoint S h (levelOneQDefault S) _ hb
  intro q _
  exact congrFun (face_parity_zero S z f h hh) q

/-- Arbitrary endpoint values and ALL neighbouring Z bits, not just one owner. -/
theorem edge_endpoint (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) :=
  one_parity_endpoint S h q (edge_parity_other S q e h hh) hb

/-- Singleton support is proved on one rigid abstract carrier before any
actual presentation/owner-family unfolding. -/
private theorem basis_has_owner {I O : Type} (owner : I → O) (q : I) :
    ∃ center : O, ∀ r : I,
      canonicalBasisWord (F := Bit) q r≠0 → owner r=center := by
  classical
  refine ⟨owner q,?_⟩
  intro r hr
  have heq : r=q := by
    by_contra hn
    have hz : canonicalBasisWord (F := Bit) q r=0 := by
      simp only [canonicalBasisWord,Pi.single_apply,if_neg hn]
    exact hr hz
  subst r
  rfl

/-- An arbitrary actual physical basis coordinate supplies its OWN actual owner. -/
theorem elementary_local (S : OddScale) (q : (C S).Q) :
    levelTwoLocalError S (canonicalBasisWord (F := Bit) q) := by
  apply (raw_owner_iff S (canonicalBasisWord (F := Bit) q)).2
  exact basis_has_owner
    (BDL26ReplacementSupport.rzCorrectionOwner (P S) S)
    (show RZQ (P S) S from q)

theorem elementary_branch (S : OddScale) (q : (C S).Q) :
    localSuccess S (delta S (canonicalBasisWord (F := Bit) q)) :=
  (localSuccess_iff S _).2 ⟨canonicalBasisWord (F := Bit) q,elementary_local S q,rfl⟩

/-- Empty-suffix physical C2 endpoint, independent of the chosen star centre. -/
theorem elementary_endpoint (S : OddScale) (q : (C S).Q) :
    ∃ p : Potential S, boundary S p=
      canonicalBasisWord (F := Bit) q+D S 0+D S (delta S (canonicalBasisWord (F := Bit) q)) := by
  rcases q with ⟨z,e⟩ | ⟨q,v⟩
  · refine one_parity_endpoint S
      (canonicalBasisWord (F := Bit) (.inl ⟨z,e⟩ : RZQ (P S) S))
      (levelOneQDefault S) ?_
      (elementary_branch S (.inl ⟨z,e⟩ : RZQ (P S) S))
    intro r _
    exact congrFun (rzQParity_localBasis (P S) S z e) r
  · refine one_parity_endpoint S
      (canonicalBasisWord (F := Bit) (.inr ⟨q,v⟩ : RZQ (P S) S)) q ?_
      (elementary_branch S (.inr ⟨q,v⟩ : RZQ (P S) S))
    intro r hr
    have hp := congrFun (rzQParity_qBasis (P S) S q v) r
    calc
      parity S (canonicalBasisWord (F := Bit) (.inr ⟨q,v⟩ : RZQ (P S) S)) r=
          canonicalBasisWord (F := Bit) q r := hp
      _ = 0 := by
        change (Pi.single q (1 : Bit) : Word Bit (P S).Q) r=0
        simp only [Pi.single_apply,if_neg hr]

/-- For arbitrary backgrounds the Z-face case has TWO original local calls. -/
theorem zero_parity_two_calls (S : OddScale) (h : Error S) (s t : Syndrome S)
    (hd : delta S h=s+t) (hp : parity S h=0)
    (hs : localSuccess S s) (ht : localSuccess S t) :
    ∃ p : Potential S, boundary S p=h+D S s+D S t := by
  obtain ⟨ws,hws⟩ := hs
  obtain ⟨wt,hwt⟩ := ht
  obtain ⟨hls,hds⟩ := returned_local_and_syndrome S s ws hws
  obtain ⟨hlt,hdt⟩ := returned_local_and_syndrome S t wt hwt
  obtain ⟨a,ha⟩ := parity_local_label S (D S s) hls (levelOneQDefault S)
  obtain ⟨b,hb⟩ := parity_local_label S (D S t) hlt (levelOneQDefault S)
  have hc : delta S (h+D S s+D S t)=0 := by
    rw [map_add,map_add,hd,hds,hdt]
    calc
      _ = (s+s)+(t+t) := by abel
      _ = 0 := by rw [twice,twice,add_zero]
  have hsup : ∀ q, parity S (h+D S s+D S t) q≠0 → q=a ∨ q=b := by
    intro q hq
    by_contra hn
    apply hq
    have hqa : q≠a := fun heq => hn (Or.inl heq)
    have hqb : q≠b := fun heq => hn (Or.inr heq)
    calc
      parity S (h+D S s+D S t) q=
          parity S (h+D S s) q+parity S (D S t) q :=
        congrFun (parity_add S (h+D S s) (D S t)) q
      _ = (parity S h q+parity S (D S s) q)+parity S (D S t) q := by
        have hmap := congrFun (parity_add S h (D S s)) q
        change parity S (h+D S s) q=parity S h q+parity S (D S s) q at hmap
        exact congrArg (fun value : Bit => value+parity S (D S t) q) hmap
      _ = 0 := by rw [hp,Pi.zero_apply,ha q hqa,hb q hqb,zero_add,zero_add]
  exact two_parity_endpoint S _ hc a b hsup

/-- Arbitrary actual nonzero/zero backgrounds, with every Z-face coefficient. -/
theorem face_two_calls (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S) (s t : Syndrome S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) (hd : delta S h=s+t)
    (hs : localSuccess S s) (ht : localSuccess S t) :
    ∃ p : Potential S, boundary S p=h+D S s+D S t :=
  zero_parity_two_calls S h s t hd (face_parity_zero S z f h hh) hs ht

/-- Identical deterministic outputs cancel even at a NONZERO input. -/
theorem repeated_input (S : OddScale) (s : Syndrome S) :
    boundary S (0 : Potential S)=(0 : Error S)+D S s+D S s := by
  rw [map_zero,zero_add,twice]

/-- Zero is in the ORIGINAL successful branch by actual owner enumeration. -/
theorem zero_branch (S : OddScale) : localSuccess S (0 : Syndrome S) := by
  apply (localSuccess_iff S 0).2
  refine ⟨0,?_,map_zero _⟩
  apply (raw_owner_iff S (0 : Error S)).2
  refine ⟨Vertex.q (levelOneQDefault S),?_⟩
  intro q hq
  exact False.elim (hq rfl)

/-- A nonzero successful raw input cannot have an individually zero correction. -/
theorem successful_nonzero_output (S : OddScale) (s : Syndrome S)
    (hs : localSuccess S s) (hne : s≠0) : D S s≠0 := by
  obtain ⟨w,hw⟩ := hs
  have hd := (returned_local_and_syndrome S s w hw).2
  intro hz
  have hdelta : delta S (D S s)=delta S (0 : Error S) := congrArg (delta S) hz
  have hzero : delta S (0 : Error S)=0 := (delta S).map_zero
  exact hne (hd.symm.trans (hdelta.trans hzero))

/-- The exact success domain is not a universal owner-preimage assertion. -/
theorem failed_branch_has_no_local_error (S : OddScale) (h : Error S)
    (hn : localSearch S (delta S h)=none) : ¬levelTwoLocalError S h := by
  intro hh
  exact (localSearch_none_iff S _).1 hn ⟨h,hh,rfl⟩

end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
