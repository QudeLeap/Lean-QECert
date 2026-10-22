import QEC.Coding.FiniteAlternatingConstruction.RZFiniteBlockTransport
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWitness
import Mathlib.Tactic

/-!
# Actual RZ physical Z-star transport

Internal project-derived refinement of BDL26 v1 `paper.tex:1939–1980,
2521–2654,3465–3481` (source file SHA256
66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
Actual incidence and the three distinct raw parents are calculated from the
original replacement. The same two canonical runs and all eleven finite-block
Pullback clauses retain full E, full potential and every neighbour Z block.
Only the lower error has the stated weight bound. No component, mask,
stability, public-theorem or lifetime claim is made.
-/
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalStarTransport

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators

/-- The actual old closed Z-star's Q-coordinate slice. -/
def physicalZStar (P : TannerSquarePresentation) (z : P.Z) : Finset P.Q :=
  Finset.univ.filter fun q => P.qz q z=true

@[simp] theorem mem_physicalZStar (P : TannerSquarePresentation) (z : P.Z) (q : P.Q) :
    q ∈ physicalZStar P z ↔ P.qz q z=true := by simp [physicalZStar]

/-- Face existence follows from the original pairing and original X root. -/
theorem physicalZStar_face_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z) (q : P.Q) :
    q ∈ physicalZStar P z ↔ ∃ f : P.Face, ∃ c : Fin 2,
      P.faceZ f=z ∧ P.faceQ f c=q := by
  rw [mem_physicalZStar]
  constructor
  · intro h
    let x := A.xqRoot q
    let shared : SharedQ P.data x.1 z := ⟨q,by simp [x.2,h]⟩
    obtain ⟨⟨f,c⟩,hc⟩ := (P.perfectPairing x.1 z).2 shared
    exact ⟨f.1,c,f.2.2,congrArg Subtype.val hc⟩
  · rintro ⟨f,c,rfl,rfl⟩
    exact P.data.faceQ_qz f c

private theorem cast_qz (U V : TannerSquarePresentation) (hp : U=V)
    (q : U.Q) (z : U.Z) :
    U.qz q z=V.qz ((Equiv.cast (congrArg TannerSquarePresentation.Q hp)) q)
      ((Equiv.cast (congrArg TannerSquarePresentation.Z hp)) z) := by
  cases hp
  rfl

private theorem cast_vertex_z_cast (U V : TannerSquarePresentation) (hp : U=V)
    (hv : Vertex U=Vertex V) (hz : U.Z=V.Z) (z : V.Z) :
    cast hv (Vertex.z ((Equiv.cast hz).symm z))=Vertex.z z := by
  cases hp
  rfl

private theorem cast_vertex_q_cast (U V : TannerSquarePresentation) (hp : U=V)
    (hv : Vertex U=Vertex V) (hq : U.Q=V.Q) (q : V.Q) :
    cast hv (Vertex.q ((Equiv.cast hq).symm q))=Vertex.q q := by
  cases hp
  rfl

private theorem basis_support {I : Type} [Fintype I] (q : I) :
    hammingSupport (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q) ⊆ {q} := by
  intro r hr
  by_contra hn
  have hne : r≠q := by simpa using hn
  have hz : canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q r=0 := by
    simp [canonicalBasisWord,Pi.single_apply,hne]
  exact (by simpa [hammingSupport] using hr : canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q r≠0) hz

private theorem basis_read {I J : Type} (e : I ≃ J)
    (R : Word BDL26FiniteTannerSquare.Field I ≃ₗ[BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field J)
    (hr : ∀ w x, R w x=w (e.symm x)) (q : J) :
    R.symm (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q)=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (e.symm q) := by
  apply R.injective
  rw [LinearEquiv.apply_symm_apply]
  funext r
  rw [hr]
  by_cases h : r=q
  · subst r
    simp [canonicalBasisWord,Pi.single_apply]
  · have hn : e.symm r≠e.symm q := fun he => h (e.symm.injective he)
    simp [canonicalBasisWord,Pi.single_apply,h,hn]

/-- A typed constant-family proof, independent of any actual carrier reduction. -/
theorem basis_nonzero {I : Type} (q : I) :
    canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ≠ (0 : Word BDL26FiniteTannerSquare.Field I) := by
  intro hz
  have hself : canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q q=(1 : BDL26FiniteTannerSquare.Field) := by
    change Pi.single (M := fun _ : I => BDL26FiniteTannerSquare.Field) q (1 : BDL26FiniteTannerSquare.Field) q=1
    exact Pi.single_eq_same (M := fun _ : I => BDL26FiniteTannerSquare.Field) q (1 : BDL26FiniteTannerSquare.Field)
  have hzero : (0 : Word BDL26FiniteTannerSquare.Field I) q=(0 : BDL26FiniteTannerSquare.Field) := rfl
  exact one_ne_zero (hself.symm.trans ((congrFun hz q).trans hzero))

private theorem twice {I : Type} (w : Word BDL26FiniteTannerSquare.Field I) : w+w=0 := by
  funext q
  exact CharTwo.add_self_eq_zero _

private theorem shift_error {I : Type} (a e : Word BDL26FiniteTannerSquare.Field I) : a+(a+e)=e := by
  rw [← add_assoc,twice,zero_add]

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

/-- Exactly the inverse of the merged actual Z chart. -/
def upperZChart : RZZ (Old S depth i) S ≃ FamilyZ S depth i.succ :=
  (coord2 S depth i odd).symm

def upperQChart : RZQ (Old S depth i) S ≃ FamilyQ S depth i.succ :=
  (coord1 S depth i odd).symm

@[simp] theorem coord2_upperZChart (z : RZZ (Old S depth i) S) :
    coord2 S depth i odd (upperZChart S depth i odd z)=z :=
  (coord2 S depth i odd).apply_symm_apply z

@[simp] theorem upperZChart_coord2 (u : FamilyZ S depth i.succ) :
    upperZChart S depth i odd (coord2 S depth i odd u)=u :=
  (coord2 S depth i odd).symm_apply_apply u

@[simp] theorem coord1_upperQChart (q : RZQ (Old S depth i) S) :
    coord1 S depth i odd (upperQChart S depth i odd q)=q :=
  (coord1 S depth i odd).apply_symm_apply q

@[simp] theorem upperQChart_coord1 (q : FamilyQ S depth i.succ) :
    upperQChart S depth i odd (coord1 S depth i odd q)=q :=
  (coord1 S depth i odd).symm_apply_apply q

/-- This is the literal qz field transported along the actual parity equality. -/
theorem actual_incidence (q : FamilyQ S depth i.succ) (u : FamilyZ S depth i.succ) :
    (state S (i.val+1)).presentation.qz q u=
      rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord1 S depth i odd q) (coord2 S depth i odd u) :=
  cast_qz _ _ (upper_eq S depth i odd) q u

/-- The computed old Z label; no owner or chart certificate is supplied. -/
def parentZ (u : FamilyZ S depth i.succ) : (Old S depth i).Z :=
  (coord2 S depth i odd u).1

def upperStar (u : FamilyZ S depth i.succ) : Finset (FamilyQ S depth i.succ) :=
  physicalZStar (state S (i.val+1)).presentation u

def Q0 (u : FamilyZ S depth i.succ) : Finset (Old S depth i).Q :=
  physicalZStar (Old S depth i) (parentZ S depth i odd u)

def Zplus (u : FamilyZ S depth i.succ) : Finset (Old S depth i).Z :=
  Coordinates.zplus (Old S depth i) (Q0 S depth i odd u) {parentZ S depth i odd u}

def Localized (u : FamilyZ S depth i.succ) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ upperStar S depth i u

theorem chart_incidence (q : RZQ (Old S depth i) S) (z : RZZ (Old S depth i) S) :
    (state S (i.val+1)).presentation.qz
      (upperQChart S depth i odd q) (upperZChart S depth i odd z)=
      rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S q z := by
  rw [actual_incidence S depth i odd,
    coord1_upperQChart S depth i odd q,coord2_upperZChart S depth i odd z]

include odd in
/-- Incident local edges have precisely the centre's old Z owner. -/
theorem raw_local_edge_owner (z z' : (Old S depth i).Z)
    (e : ZDoubleCylinderEdge (Old S depth i) z S)
    (v : ZDoubleCylinderVertex (Old S depth i) z' S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inl ⟨z,e⟩) ⟨z',v⟩=true) : z'=z := by
  change decide (∃ he : z'=z,
    doubleCylinderEdgeVertexMatrix (transposePresentation (Old S depth i)) z S (he ▸ v) e=1)=true at hi
  exact (of_decide_eq_true hi).choose

include odd in
/-- The Q-cylinder constructor projects to the original qz incidence. -/
theorem raw_q_vertex_owner (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S)
    (w : ZDoubleCylinderVertex (Old S depth i) z S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inr ⟨q,v⟩) ⟨z,w⟩=true) : (Old S depth i).qz q z=true := by
  change decide (∃ hqz : (Old S depth i).qz q z=true,
    qToZDoubleCylinderVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
      q z hqz S v=w)=true at hi
  exact (of_decide_eq_true hi).choose

/-- A physical incidence star is contained in computed finite input blocks. -/
theorem upperStar_subset_inputBlocks (u : FamilyZ S depth i.succ) :
    upperStar S depth i u ⊆ inputBlocks S depth i odd
      (Q0 S depth i odd u) {parentZ S depth i odd u} := by
  intro q hq
  have hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (coord1 S depth i odd q) (coord2 S depth i odd u)=true :=
    (actual_incidence S depth i odd q u).symm.trans ((mem_physicalZStar _ _ _).mp hq)
  rcases hz : coord2 S depth i odd u with ⟨z,v⟩
  rcases hc : coord1 S depth i odd q with ⟨w,e⟩ | ⟨w,t⟩
  · have hw : z=w := raw_local_edge_owner S depth i odd w z e v (by simpa only [hc,hz] using hi)
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hc,Coordinates.mem_zBlocks_z]
    simp [parentZ,hz,hw]
  · have hw : (Old S depth i).qz w z=true :=
      raw_q_vertex_owner S depth i odd w z t v (by simpa only [hc,hz] using hi)
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hc,Coordinates.mem_qBlocks_q]
    simpa [Q0,parentZ,hz] using hw

/-- Whole-Vertex transport computes the actual existing partial parent. -/
theorem centre_parent (z : (Old S depth i).Z)
    (v : ZDoubleCylinderVertex (Old S depth i) z S) :
    parent S (i.val+1) (Vertex.z (upperZChart S depth i odd ⟨z,v⟩))=some (Vertex.z z) := by
  simp only [parent,nextParent,dif_neg odd,nextRZVertex,upperZChart,coord2]
  erw [cast_vertex_z_cast _ _ (upper_eq S depth i odd)]
  rfl

theorem parent_computed (u : FamilyZ S depth i.succ) :
    parent S (i.val+1) (Vertex.z u)=some (Vertex.z (parentZ S depth i odd u)) := by
  obtain ⟨⟨z,v⟩,rfl⟩ := (upperZChart S depth i odd).surjective u
  simpa [parentZ] using centre_parent S depth i odd z v

theorem local_edge_parent_none (z : (Old S depth i).Z)
    (e : ZDoubleCylinderEdge (Old S depth i) z S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i odd (.inl ⟨z,e⟩)))=none := by
  simp only [parent,nextParent,dif_neg odd,nextRZVertex,upperQChart,coord1]
  erw [cast_vertex_q_cast _ _ (upper_eq S depth i odd)]
  rfl

theorem q_vertex_parent (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i odd (.inr ⟨q,v⟩)))=some (Vertex.q q) := by
  simp only [parent,nextParent,dif_neg odd,nextRZVertex,upperQChart,coord1]
  erw [cast_vertex_q_cast _ _ (upper_eq S depth i odd)]
  rfl

theorem localized_blocks (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (Q0 S depth i odd u) {parentZ S depth i odd u} :=
  he.trans (upperStar_subset_inputBlocks S depth i odd u)

theorem incident_card_le_seven (z : (Old S depth i).Z) :
    (physicalZStar (Old S depth i) z).card ≤ 7 := by
  have hd := BDL26GraphQuantitativeBounds.state_tannerDegree_le S i.val (Vertex.z z)
  rw [BDL26GraphQuantitativeBounds.tannerDegree,
    Fintype.card_congr (BDL26GraphQuantitativeBounds.zNeighborEquiv _ z)] at hd
  simpa [physicalZStar,Fintype.card_subtype] using hd

/-- This optional upper-star bound says nothing about the full corrected words. -/
theorem upperStar_card_le_seven (u : FamilyZ S depth i.succ) :
    (upperStar S depth i u).card ≤ 7 := by
  have hd := BDL26GraphQuantitativeBounds.state_tannerDegree_le S (i.val+1) (Vertex.z u)
  change Fintype.card {w : Vertex (state S (i.val+1)).presentation //
    tannerAdjacent (state S (i.val+1)).presentation (Vertex.z u) w} ≤ 7 at hd
  have he := Fintype.card_congr
    (BDL26GraphQuantitativeBounds.zNeighborEquiv (state S (i.val+1)).presentation u)
  have hcard : Fintype.card {q : (state S (i.val+1)).presentation.Q //
      (state S (i.val+1)).presentation.qz q u=true} ≤ 7 := he ▸ hd
  simpa [upperStar,physicalZStar,Fintype.card_subtype] using hcard

include odd in
theorem above_iff : 2 ≤ i.val ↔ 3 ≤ i.val := by omega

theorem lower_supported (above : 3 ≤ i.val) (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (lowerError S depth i odd a b) ⊆ Q0 S depth i odd u := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega)
    _ _ a b (localized_blocks S depth i odd u a b he)
  exact hp.2.2.2.2.1

theorem lower_weight (above : 3 ≤ i.val) (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧
      (Q0 S depth i odd u).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (lower_supported S depth i odd above u a b he),
    incident_card_le_seven S depth i (parentZ S depth i odd u)⟩

theorem correction_difference_supported (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Zplus S depth i odd u) :=
  BDL26RZFiniteBlockTransport.correction_difference_support S depth i odd _ _ a b
    (localized_blocks S depth i odd u a b he)

theorem input_syndrome_supported (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((errorSyndrome S depth i a).val+(errorSyndrome S depth i b).val) ⊆
      syndromeBlocks S depth i odd (Zplus S depth i odd u) :=
  BDL26RZFiniteBlockTransport.input_syndrome_support S depth i odd _ _ a b
    (localized_blocks S depth i odd u a b he)

/-- The literal original eleven clauses, plus computed parent and measured weight. -/
theorem two_run (above : 3 ≤ i.val) (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z (parentZ S depth i odd u)) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ copy : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,copy))=0) := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega)
    _ _ a b (localized_blocks S depth i odd u a b he)
  refine ⟨p,hp,parent_computed S depth i odd u,
    (lower_weight S depth i odd above u a b he).1.trans
      (lower_weight S depth i odd above u a b he).2,?_⟩
  exact potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1

/-- Both copy tags vanish on the SAME full potential in a physical pullback. -/
theorem oldX_zero (u : FamilyZ S depth i.succ) (a b : Upper S depth i) (p : Potential S depth i)
    (hp : Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p)
    (x : (Old S depth i).X) (copy : BDL26FiniteTannerSquare.Two) : read0 S depth i odd p (.inr (x,copy))=0 :=
  potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1 x copy

/-- This is the full updated error from the SAME two original runs. -/
theorem updated_eq_full (a b : Upper S depth i) :
    updated S depth i odd a b=a+b+(run S depth i odd a).correction+
      (run S depth i odd b).correction := rfl

/-- Every original actual physical basis has a support-derived endpoint. -/
theorem basis_localized (u : FamilyZ S depth i.succ) (q : FamilyQ S depth i.succ)
    (hq : (state S (i.val+1)).presentation.qz q u=true) (a : Upper S depth i) :
    Localized S depth i u a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q) := by
  change hammingSupport (a+(a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q)) ⊆ _
  rw [shift_error]
  exact (basis_support q).trans (by
    intro r hr
    have hrq : r=q := by simpa using hr
    subst r
    exact (mem_physicalZStar _ _ _).mpr hq)

/-- Materialized Q incidence supplies its actual Z centre, preserving its copy. -/
def qCentre (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) : FamilyZ S depth i.succ :=
  upperZChart S depth i odd ⟨z,qToZDoubleCylinderVertex (Old S depth i)
    (state S i.val).admissible.toTannerSquareAdmissible q z hqz S v⟩

def physicalQ (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) : FamilyQ S depth i.succ :=
  upperQChart S depth i odd (.inr ⟨q,v⟩)

theorem physicalQ_incident (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (state S (i.val+1)).presentation.qz (physicalQ S depth i odd q v)
      (qCentre S depth i odd q z hqz v)=true := by
  rw [physicalQ,qCentre,chart_incidence]
  change decide (∃ h : (Old S depth i).qz q z=true,
    qToZDoubleCylinderVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
      q z h S v=qToZDoubleCylinderVertex (Old S depth i)
        (state S i.val).admissible.toTannerSquareAdmissible q z hqz S v)=true
  exact decide_eq_true ⟨hqz,rfl⟩

@[simp] theorem qCentre_parentZ (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    parentZ S depth i odd (qCentre S depth i odd q z hqz v)=z := by simp [parentZ,qCentre]

/-- The physical global BDL26FiniteTannerSquare.Field basis equals the original chart-reindexed basis. -/
theorem physicalQ_basis (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (read1 S depth i odd).symm (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (Sum.inr ⟨q,v⟩))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q v) :=
  basis_read (coord1 S depth i odd) (read1 S depth i odd) (read1_apply S depth i odd)
    (Sum.inr ⟨q,v⟩)

/-- The lower word is the fixed original q basis, for arbitrary background a. -/
theorem lower_physicalQ_basis (a : Upper S depth i) (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    lowerError S depth i odd a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q v))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q := by
  have h := lowerError_physical_q_basis S depth i odd a q v
  exact (congrArg (fun w : Upper S depth i => lowerError S depth i odd a (a+w))
    (physicalQ_basis S depth i odd q v)).symm.trans h

/-- Both raw parents and the nonzero lower word accompany the complete pullback. -/
theorem physicalQ_transport (above : 3 ≤ i.val) (a : Upper S depth i)
    (q : (Old S depth i).Q) (z : (Old S depth i).Z) (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    let u := qCentre S depth i odd q z hqz v
    let r := physicalQ S depth i odd q v
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z z) ∧
      parent S (i.val+1) (Vertex.q r)=some (Vertex.q q) ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 7 := by
  dsimp only
  have he := basis_localized S depth i _ _ (physicalQ_incident S depth i odd q z hqz v) a
  obtain ⟨p,hp,hparent,hw,hx⟩ := two_run S depth i odd above _ _ _ he
  have hl := lower_physicalQ_basis S depth i odd a q v
  refine ⟨p,hp,?_,q_vertex_parent S depth i odd q v,hl,?_,hw⟩
  · simpa only [qCentre_parentZ] using hparent
  · intro hz
    exact basis_nonzero q (hl.symm.trans hz)

/-- A vertical local edge has literal incidence at its copy-zero endpoint. -/
def verticalPhysical (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    FamilyQ S depth i.succ := upperQChart S depth i odd (.inl ⟨z,Sum.inr v⟩)

def verticalCentre (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    FamilyZ S depth i.succ := upperZChart S depth i odd ⟨z,(0,v.1)⟩

theorem vertical_incident (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    (state S (i.val+1)).presentation.qz (verticalPhysical S depth i odd z v)
      (verticalCentre S depth i odd z v)=true := by
  rw [verticalPhysical,verticalCentre,chart_incidence]
  change decide (∃ h : z=z,
    doubleCylinderEdgeVertexMatrix (transposePresentation (Old S depth i)) z S
      (h ▸ (0,v.1)) (Sum.inr v)=1)=true
  apply decide_eq_true
  exact ⟨rfl,by simp [doubleCylinderEdgeVertexMatrix]⟩

/-- A local Z-edge perturbation has zero lower error but retains full E as a boundary. -/
theorem local_edge_transport (above : 3 ≤ i.val) (a : Upper S depth i)
    (z : (Old S depth i).Z) (e : ZDoubleCylinderEdge (Old S depth i) z S) :
    let r := upperQChart S depth i odd (.inl ⟨z,e⟩)
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by
  dsimp only
  apply one_z_block S depth i odd (by omega) z
  rw [shift_error]
  apply (basis_support _).trans
  intro q hq
  have hq' : q=upperQChart S depth i odd (.inl ⟨z,e⟩) := by simpa using hq
  subst q
  simp [zBlocks,Coordinates.zBlocks]

/-- An actual incidence example with parented centre and unparented Q coordinate. -/
theorem vertical_parents (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    (state S (i.val+1)).presentation.qz (verticalPhysical S depth i odd z v)
      (verticalCentre S depth i odd z v)=true ∧
    parent S (i.val+1) (Vertex.q (verticalPhysical S depth i odd z v))=none ∧
    parent S (i.val+1) (Vertex.z (verticalCentre S depth i odd z v))=some (Vertex.z z) :=
  ⟨vertical_incident S depth i odd z v,local_edge_parent_none S depth i odd z _,
    centre_parent S depth i odd z _⟩

/-- Actual recursively retained labels provide nonemptiness, not a hypothesis. -/
def retainedQ : (Old S depth i).Q :=
  (Old S depth i).faceQ (BDL26UniformHistoryObstruction.retainedFace S i.val) 0

def retainedZ : (Old S depth i).Z :=
  (Old S depth i).faceZ (BDL26UniformHistoryObstruction.retainedFace S i.val)

theorem retained_incidence : (Old S depth i).qz (retainedQ S depth i) (retainedZ S depth i)=true :=
  (Old S depth i).data.faceQ_qz (BDL26UniformHistoryObstruction.retainedFace S i.val) 0

/-- A literal boundary vertex derived from the retained face and original dictionary. -/
def retainedBoundaryVertex :
    SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) (retainedZ S depth i) S :=
  subdivisionOriginalBoundaryVertex (transposePresentation (Old S depth i)) (retainedZ S depth i) S
    ((transposeXStarBoundaryVertexEquiv (Old S depth i) (retainedZ S depth i)).symm
      (qToZBoundaryVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
        (retainedQ S depth i) (retainedZ S depth i) (retained_incidence S depth i) (.inl ())))

/-- No nonemptiness or incidence witness is supplied for this actual vertical example. -/
theorem retained_vertical_parents :
    (state S (i.val+1)).presentation.qz
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))=true ∧
    parent S (i.val+1) (Vertex.q
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=none ∧
    parent S (i.val+1) (Vertex.z
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=
        some (Vertex.z (retainedZ S depth i)) :=
  vertical_parents S depth i odd _ _

/-- Every copy and subdivision coordinate gives a genuine actual nonzero example. -/
theorem retained_transport (above : 3 ≤ i.val) (a : Upper S depth i) (copy : BDL26FiniteTannerSquare.Two)
    (v : QSubdivisionVertex (transposePresentation (Old S depth i)) (retainedQ S depth i) S) :
    let q := retainedQ S depth i
    let z := retainedZ S depth i
    let u := qCentre S depth i odd q z (retained_incidence S depth i) (copy,v)
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q (copy,v))
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z z) ∧
      parent S (i.val+1) (Vertex.q (physicalQ S depth i odd q (copy,v)))=some (Vertex.q q) ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 7 :=
  physicalQ_transport S depth i odd above a _ _ (retained_incidence S depth i) (copy,v)

/-- Equal errors retain an actual zero potential without normalizing chosen local cycles. -/
theorem self_localized (u : FamilyZ S depth i.succ) (a : Upper S depth i) :
    Localized S depth i u a a := by
  change hammingSupport (a+a) ⊆ _
  rw [twice]
  simp [hammingSupport]

theorem updated_self (a : Upper S depth i) : updated S depth i odd a a=0 := by
  unfold updated
  rw [twice,zero_add,twice]

/-- An actual zero potential satisfies all eleven physical clauses for equal inputs. -/
theorem self_zero_potential (u : FamilyZ S depth i.succ) (a : Upper S depth i) :
    Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a a 0 := by
  have zero_support {I : Type} [Fintype I] : hammingSupport (0 : Word BDL26FiniteTannerSquare.Field I)=∅ := by
    ext q
    simp [hammingSupport]
  simp only [Pullback,lowerError,twice,map_zero,updated_self,zero_add,add_zero,
    zero_support,Finset.empty_subset,and_self]

/-- Mixed physical perturbations remain in the same actual star. -/
theorem add_localized (u : FamilyZ S depth i.succ) (a e f : Upper S depth i)
    (he : hammingSupport e ⊆ upperStar S depth i u)
    (hf : hammingSupport f ⊆ upperStar S depth i u) :
    Localized S depth i u a (a+(e+f)) := by
  change hammingSupport (a+(a+(e+f))) ⊆ _
  rw [shift_error]
  intro q hq
  by_contra hn
  have he0 : e q=0 := by
    by_contra h
    exact hn (he (by simpa [hammingSupport] using h))
  have hf0 : f q=0 := by
    by_contra h
    exact hn (hf (by simpa [hammingSupport] using h))
  exact (by simpa [hammingSupport] using hq : (e+f) q≠0) (by simp [he0,hf0])

/-- Two incident coordinates may overlap or cancel; no support certificate is assumed. -/
theorem mixed_basis_localized (u : FamilyZ S depth i.succ)
    (r t : FamilyQ S depth i.succ)
    (hr : (state S (i.val+1)).presentation.qz r u=true)
    (ht : (state S (i.val+1)).presentation.qz t u=true) (a : Upper S depth i) :
    Localized S depth i u a
      (a+(canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r+
        canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) t)) := by
  apply add_localized S depth i u a
  · simpa only [Localized,zero_add] using basis_localized S depth i u r hr (0 : Upper S depth i)
  · simpa only [Localized,zero_add] using basis_localized S depth i u t ht (0 : Upper S depth i)

theorem repeated_perturbation (a e : Upper S depth i) : a+(e+e)=a := by rw [twice,add_zero]

/-- No above-C2 RZ endpoint exists at physical depth at most two. -/
theorem no_small_depth (small : depth ≤ 2) : ¬ 3 ≤ i.val := by omega

/-- All original stopped snapshots at physical depth 2*j+4, with full p and Pullback. -/
theorem top_history_two_run (j : Nat)
    (u : FamilyZ S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j)
        (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
        {parentZ S (2*j+4) (topStep j) (topStep_odd j) u} a b p ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
          (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p ∧
      (indexedFamily S (2*j+4)).coboundary1 (topStep j).castSucc
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        (topOutput S j a).coarse.val+(topOutput S j b).coarse.val ∧
      parent S ((topStep j).val+1) (Vertex.z u)=
        some (Vertex.z (parentZ S (2*j+4) (topStep j) (topStep_odd j) u)) ∧
      HammingWeight (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b) ≤ 7 ∧
      (∀ x : (Old S (2*j+4) (topStep j)).X, ∀ copy : BDL26FiniteTannerSquare.Two,
        read0 S (2*j+4) (topStep j) (topStep_odd j) p (.inr (x,copy))=0) := by
  obtain ⟨p,hp,hm,hs⟩ := BDL26RZFiniteBlockTransport.top_history_two_run S j _ _ a b
    (localized_blocks S (2*j+4) (topStep j) (topStep_odd j) u a b he)
  refine ⟨p,hp,hm,hs,parent_computed S (2*j+4) (topStep j) (topStep_odd j) u,?_,?_⟩
  · exact (lower_weight S (2*j+4) (topStep j) (topStep_odd j) (by simp [topStep]) u a b he).1.trans
      (lower_weight S (2*j+4) (topStep j) (topStep_odd j) (by simp [topStep]) u a b he).2
  · exact potential_oldX_zero S (2*j+4) (topStep j) (topStep_odd j) _ _ p
      hp.2.2.2.2.2.2.2.2.1

end QEC.Coding.BDL26RZPhysicalStarTransport
