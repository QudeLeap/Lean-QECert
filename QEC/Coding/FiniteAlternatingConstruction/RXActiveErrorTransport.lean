import QEC.Coding.FiniteAlternatingConstruction.RXFiniteBlockTransport
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds

/-!
# Active original-error blocks and unconditional RX weight transport

Project-derived internal mathematics in the BDL26 v1 construction. The actual
coarse relation (`paper.tex:2325–2384`) and X-error cleaning (`3136–3185`)
motivate the same-U transport. Active labels below are extracted from full
physical ERROR support, independently of running the decoder. The numerical
constant seven comes from the proved actual recursive Tanner valence. This
is a single-step weight theorem, with no parent-confinement, history, stability,
logical-protection, or lifetime conclusion.
-/
noncomputable section
namespace QEC.Coding.BDL26RXActiveErrorTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

/-- Literal original X-region intersections with the full physical error support. -/
def xPiece (E : Upper S depth i) (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLx S depth i h).correctionRegion x ∩ hammingSupport E

def qPiece (E : Upper S depth i) (q : QCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLq S depth i h).correctionRegion q ∩ hammingSupport E

def activeX (E : Upper S depth i) : Finset (XCoord S i) :=
  Finset.univ.filter fun x => (xPiece S depth i h E x).Nonempty

def activeQ (E : Upper S depth i) : Finset (QCoord S i) :=
  Finset.univ.filter fun q => (qPiece S depth i h E q).Nonempty

private theorem support_mem {F α : Type*} [Zero F] [DecidableEq F] [Fintype α]
    (E : Word F α) (p : α) : p ∈ hammingSupport E ↔ E p≠0 := by
  simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_activeX (E : Upper S depth i) (x : XCoord S i) :
    x ∈ activeX S depth i h E ↔ (xPiece S depth i h E x).Nonempty := by
  simp only [activeX,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_activeQ (E : Upper S depth i) (q : QCoord S i) :
    q ∈ activeQ S depth i h E ↔ (qPiece S depth i h E q).Nonempty := by
  simp only [activeQ,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_activeX_iff (E : Upper S depth i) (x : XCoord S i) :
    x ∈ activeX S depth i h E ↔ ∃ p ∈ (rxLx S depth i h).correctionRegion x, E p≠0 := by
  rw [mem_activeX]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(Finset.mem_inter.mp hp).1,(support_mem E p).mp (Finset.mem_inter.mp hp).2⟩
  · rintro ⟨p,hp,hn⟩
    exact ⟨p,Finset.mem_inter.mpr ⟨hp,(support_mem E p).mpr hn⟩⟩

theorem mem_activeQ_iff (E : Upper S depth i) (q : QCoord S i) :
    q ∈ activeQ S depth i h E ↔ ∃ p ∈ (rxLq S depth i h).correctionRegion q, E p≠0 := by
  rw [mem_activeQ]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(Finset.mem_inter.mp hp).1,(support_mem E p).mp (Finset.mem_inter.mp hp).2⟩
  · rintro ⟨p,hp,hn⟩
    exact ⟨p,Finset.mem_inter.mpr ⟨hp,(support_mem E p).mpr hn⟩⟩

theorem inactive_x_iff (E : Upper S depth i) (x : XCoord S i) :
    x ∉ activeX S depth i h E ↔
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) E=0 := by
  constructor
  · intro hx
    funext p
    by_contra hn
    exact hx ((mem_activeX_iff S depth i h E x).mpr ⟨p.val,p.property,hn⟩)
  · intro hz hx
    obtain ⟨p,hp,hn⟩ := (mem_activeX_iff S depth i h E x).mp hx
    exact hn (congrFun hz ⟨p,hp⟩)

theorem inactive_q_iff (E : Upper S depth i) (q : QCoord S i) :
    q ∉ activeQ S depth i h E ↔
      restrictWordLinear ((rxLq S depth i h).correctionRegion q) E=0 := by
  constructor
  · intro hq
    funext p
    by_contra hn
    exact hq ((mem_activeQ_iff S depth i h E q).mpr ⟨p.val,p.property,hn⟩)
  · intro hz hq
    obtain ⟨p,hp,hn⟩ := (mem_activeQ_iff S depth i h E q).mp hq
    exact hn (congrFun hz ⟨p,hp⟩)

theorem active_x_of_restriction_ne_zero (E : Upper S depth i) (x : XCoord S i)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    x ∈ activeX S depth i h E := by
  by_contra hx
  exact hn ((inactive_x_iff S depth i h E x).mp hx)

theorem active_q_of_restriction_ne_zero (E : Upper S depth i) (q : QCoord S i)
    (hn : restrictWordLinear ((rxLq S depth i h).correctionRegion q) E≠0) :
    q ∈ activeQ S depth i h E := by
  by_contra hq
  exact hn ((inactive_q_iff S depth i h E q).mp hq)

/-- These are the instantiated original decoder regions, covering every physical coordinate. -/
theorem correction_regions_cover :
    (Finset.univ.biUnion ((rxLx S depth i h).correctionRegion)) ∪
      (Finset.univ.biUnion ((rxLq S depth i h).correctionRegion))=Finset.univ := by
  have hc := (rxData S depth i h).correction_sectors_cover
  rw [(rxData S depth i h).qCorrectionSector_eq_regions] at hc
  exact hc

theorem x_regions_disjoint (x y : XCoord S i) (hn : x≠y) :
    Disjoint ((rxLx S depth i h).correctionRegion x) ((rxLx S depth i h).correctionRegion y) :=
  (rxData S depth i h).cx_correction_regions_pairwise_disjoint x y hn

theorem q_regions_disjoint (q r : QCoord S i) (hn : q≠r) :
    Disjoint ((rxLq S depth i h).correctionRegion q) ((rxLq S depth i h).correctionRegion r) :=
  (rxData S depth i h).cq_correction_regions_pairwise_disjoint q r hn

theorem x_q_regions_disjoint (x : XCoord S i) (q : QCoord S i) :
    Disjoint ((rxLx S depth i h).correctionRegion x) ((rxLq S depth i h).correctionRegion q) :=
  x_q_disjoint S depth i h x q

theorem x_pieces_disjoint (E : Upper S depth i) (x y : XCoord S i) (hn : x≠y) :
    Disjoint (xPiece S depth i h E x) (xPiece S depth i h E y) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.disjoint_left.mp (x_regions_disjoint S depth i h x y hn))
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1

theorem q_pieces_disjoint (E : Upper S depth i) (q r : QCoord S i) (hn : q≠r) :
    Disjoint (qPiece S depth i h E q) (qPiece S depth i h E r) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.disjoint_left.mp (q_regions_disjoint S depth i h q r hn))
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1

theorem active_piece_unions_disjoint (E : Upper S depth i) :
    Disjoint ((activeX S depth i h E).biUnion (xPiece S depth i h E))
      ((activeQ S depth i h E).biUnion (qPiece S depth i h E)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hq
  exact (Finset.disjoint_left.mp (x_q_regions_disjoint S depth i h x q))
    (Finset.mem_inter.mp hpx).1 (Finset.mem_inter.mp hpq).1

/-- Exact labelled partition of full physical ERROR support, with empty pieces omitted only as inactive labels. -/
theorem support_partition (E : Upper S depth i) :
    (activeX S depth i h E).biUnion (xPiece S depth i h E) ∪
      (activeQ S depth i h E).biUnion (qPiece S depth i h E)=hammingSupport E := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hx).2
    · obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hq).2
  · intro hp
    have hc : p ∈ (Finset.univ.biUnion ((rxLx S depth i h).correctionRegion)) ∪
        (Finset.univ.biUnion ((rxLq S depth i h).correctionRegion)) := by
      rw [correction_regions_cover S depth i h]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hc
      have hm : p ∈ xPiece S depth i h E x := Finset.mem_inter.mpr ⟨hx,hp⟩
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x,(mem_activeX S depth i h E x).mpr ⟨p,hm⟩,hm⟩)
    · obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hc
      have hm : p ∈ qPiece S depth i h E q := Finset.mem_inter.mpr ⟨hq,hp⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨q,(mem_activeQ S depth i h E q).mpr ⟨p,hm⟩,hm⟩)

theorem error_localized (E : Upper S depth i) :
    hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h (activeX S depth i h E) ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h (activeQ S depth i h E) := by
  intro p hp
  have hm := (support_partition S depth i h E).symm ▸ hp
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hp).1⟩)
  · obtain ⟨q,hq,hp⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,hq,(Finset.mem_inter.mp hp).1⟩)

private theorem card_biUnion_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (J : Finset α) (Y : α → Finset β) (hd : ∀ x y, x≠y → Disjoint (Y x) (Y y)) :
    (J.biUnion Y).card=∑ x ∈ J, (Y x).card := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert x J hx ih =>
    have hu : Disjoint (Y x) (J.biUnion Y) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨y,hy,hpy⟩ := Finset.mem_biUnion.mp hq
      exact (Finset.disjoint_left.mp (hd x y (fun he => hx (he.symm ▸ hy)))) hp hpy
    rw [Finset.biUnion_insert,Finset.card_union_of_disjoint hu,ih,Finset.sum_insert hx]

theorem support_count (E : Upper S depth i) :
    (∑ x ∈ activeX S depth i h E, (xPiece S depth i h E x).card) +
      (∑ q ∈ activeQ S depth i h E, (qPiece S depth i h E q).card)=HammingWeight E := by
  rw [← card_biUnion_disjoint _ _ (x_pieces_disjoint S depth i h E),
    ← card_biUnion_disjoint _ _ (q_pieces_disjoint S depth i h E),
    ← Finset.card_union_of_disjoint (active_piece_unions_disjoint S depth i h E),
    support_partition S depth i h]
  rfl

theorem active_count_le_weight (E : Upper S depth i) :
    (activeX S depth i h E).card+(activeQ S depth i h E).card ≤ HammingWeight E := by
  have hx : (activeX S depth i h E).card ≤ ∑ x ∈ activeX S depth i h E, (xPiece S depth i h E x).card := by
    calc
      _ = ∑ _x ∈ activeX S depth i h E, (1 : Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => Nat.succ_le_of_lt
        (Finset.card_pos.mpr ((mem_activeX S depth i h E x).mp hx)))
  have hq : (activeQ S depth i h E).card ≤ ∑ q ∈ activeQ S depth i h E, (qPiece S depth i h E q).card := by
    calc
      _ = ∑ _q ∈ activeQ S depth i h E, (1 : Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => Nat.succ_le_of_lt
        (Finset.card_pos.mpr ((mem_activeQ S depth i h E q).mp hq)))
  exact (Nat.add_le_add hx hq).trans_eq (support_count S depth i h E)

@[simp] theorem activeX_zero : activeX S depth i h (0 : Upper S depth i)=∅ := by
  simp [activeX,xPiece]

@[simp] theorem activeQ_zero : activeQ S depth i h (0 : Upper S depth i)=∅ := by
  simp [activeQ,qPiece]

theorem both_active_empty_iff (E : Upper S depth i) :
    activeX S depth i h E=∅ ∧ activeQ S depth i h E=∅ ↔ E=0 := by
  constructor
  · rintro ⟨hx,hq⟩
    have hp := support_partition S depth i h E
    rw [hx,hq,Finset.biUnion_empty,Finset.biUnion_empty,Finset.empty_union] at hp
    apply (HammingWeight_eq_zero_iff E).mp
    change (hammingSupport E).card=0
    rw [← hp]
    rfl
  · intro he
    subst E
    exact ⟨activeX_zero S depth i h,activeQ_zero S depth i h⟩

@[simp] theorem activeX_self (a : Upper S depth i) : activeX S depth i h (a+a)=∅ := by
  rw [word_add_self,activeX_zero]

@[simp] theorem activeQ_self (a : Upper S depth i) : activeQ S depth i h (a+a)=∅ := by
  rw [word_add_self,activeQ_zero]

/-- Original incident labels are identified with the actual measured incidence subtype. -/
def incidentEquiv (x : XCoord S i) :
    {q : QCoord S i // q ∈ incidentQ S depth i x} ≃
      {q : QCoord S i // (state S i.val).presentation.xq x q=true} where
  toFun q := ⟨q.val,(mem_incidentQ S depth i x q.val).mp q.property⟩
  invFun q := ⟨q.val,(mem_incidentQ S depth i x q.val).mpr q.property⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

theorem incident_card_eq_xDegree (x : XCoord S i) :
    (incidentQ S depth i x).card=xDegree (state S i.val).presentation x := by
  simpa only [Fintype.card_coe,xDegree] using Fintype.card_congr (incidentEquiv S depth i x)

theorem incident_card_eq_tannerDegree (x : XCoord S i) :
    (incidentQ S depth i x).card=tannerDegree (state S i.val).presentation (.x x) := by
  rw [incident_card_eq_xDegree,xDegree,tannerDegree,
    Fintype.card_congr (xNeighborEquiv (state S i.val).presentation x)]

/-- Seven is derived from the recursively instantiated actual Tanner degree. -/
theorem incident_card_le_seven (x : XCoord S i) : (incidentQ S depth i x).card ≤ 7 := by
  rw [incident_card_eq_tannerDegree]
  exact state_tannerDegree_le S i.val (.x x)

def N (a b : Upper S depth i) : Finset (QCoord S i) :=
  BDL26RXFiniteBlockTransport.neighbors S depth i (activeX S depth i h (a+b)) (activeQ S depth i h (a+b))

def Phi (a b : Upper S depth i) : Potential S depth i :=
  BDL26RXFiniteBlockTransport.Phi S depth i h (activeX S depth i h (a+b)) a b

def R (a b : Upper S depth i) : Upper S depth i :=
  BDL26RXFiniteBlockTransport.R S depth i h (activeX S depth i h (a+b)) a b

def L (a b : Upper S depth i) : Lower S depth i :=
  BDL26RXFiniteBlockTransport.L S depth i h (activeX S depth i h (a+b)) a b

def NZ (a b : Upper S depth i) : Finset (ZCoord S i) :=
  BDL26RXFiniteBlockTransport.neighborZ S depth i (activeX S depth i h (a+b)) (activeQ S depth i h (a+b))

theorem localized (a b : Upper S depth i) :
    BDL26RXFiniteBlockTransport.Localized S depth i h
      (activeX S depth i h (a+b)) (activeQ S depth i h (a+b)) a b :=
  error_localized S depth i h (a+b)

theorem map1_eq_remainder (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b)=R S depth i h a b :=
  BDL26RXFiniteBlockTransport.map1_eq_remainder S depth i h _ _ a b (localized S depth i h a b)

theorem map1_with_potential (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) :=
  BDL26RXFiniteBlockTransport.map1_with_potential S depth i h _ _ a b (localized S depth i h a b)

theorem lower_syndrome (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val :=
  BDL26RXFiniteBlockTransport.lower_syndrome S depth i h _ _ a b (localized S depth i h a b)

theorem potential_supported (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h a b) ⊆
      BDL26RXFiniteBlockTransport.degreeZeroBlocks S depth i h (activeX S depth i h (a+b)) :=
  BDL26RXFiniteBlockTransport.phi_supported S depth i h _ a b

theorem lower_supported (a b : Upper S depth i) : hammingSupport (L S depth i h a b) ⊆ N S depth i h a b :=
  BDL26RXFiniteBlockTransport.lower_supported S depth i h _ _ a b (localized S depth i h a b)

theorem remainder_x_zero (a b : Upper S depth i) (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (R S depth i h a b)=0 :=
  BDL26RXFiniteBlockTransport.remainder_x_zero S depth i h _ _ x a b (localized S depth i h a b)

theorem coarse_apply (a b : Upper S depth i) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z = ∑ q ∈ N S depth i h a b, L S depth i h a b q *
      (if (state S i.val).presentation.qz q z=true then 1 else 0) :=
  BDL26RXFiniteBlockTransport.coarse_apply S depth i h _ _ a b (localized S depth i h a b) z

theorem coarse_supported (a b : Upper S depth i) : hammingSupport (coarseSum S depth i h a b).val ⊆ NZ S depth i h a b :=
  BDL26RXFiniteBlockTransport.coarse_supported S depth i h _ _ a b (localized S depth i h a b)

theorem selected_image_support_eq (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val) =
      (hammingSupport (coarseSum S depth i h a b).val).biUnion (zPairImage (rxData S depth i h)) :=
  BDL26RXFiniteBlockTransport.selected_image_support_eq S depth i h a b

theorem selected_image_supported (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val) ⊆
      (NZ S depth i h a b).biUnion (zPairImage (rxData S depth i h)) :=
  BDL26RXFiniteBlockTransport.selected_image_supported S depth i h _ _ a b (localized S depth i h a b)

theorem selected_image_pair (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=(coarseSum S depth i h a b).val z :=
  BDL26RXFiniteBlockTransport.selected_image_pair S depth i h a b z copy

theorem selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 :=
  BDL26RXFiniteBlockTransport.selected_image_exterior S depth i h a b p hp

theorem lower_weight_le_neighbors (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (N S depth i h a b).card :=
  BDL26RXFiniteBlockTransport.lower_card_le S depth i h _ _ a b (localized S depth i h a b)

theorem neighbors_card_le_sharp (a b : Upper S depth i) :
    (N S depth i h a b).card ≤ (activeQ S depth i h (a+b)).card +
      ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card :=
  BDL26RXFiniteBlockTransport.neighbors_card_le S depth i _ _

theorem sharp_le_seven_activeX (a b : Upper S depth i) :
    (activeQ S depth i h (a+b)).card + ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card ≤
      (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card := by
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _x ∈ activeX S depth i h (a+b), (7 : Nat) :=
      Finset.sum_le_sum (fun x _ => incident_card_le_seven S depth i x)
    _ = _ := by simp [Nat.mul_comm]

theorem seven_activeX_le_seven_count (a b : Upper S depth i) :
    (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card ≤
      7*((activeX S depth i h (a+b)).card+(activeQ S depth i h (a+b)).card) := by omega

theorem lower_weight_le_sharp (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (activeQ S depth i h (a+b)).card +
      ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card :=
  (lower_weight_le_neighbors S depth i h a b).trans (neighbors_card_le_sharp S depth i h a b)

/-- Unconditional single-step bound by original physical ERROR weight. -/
theorem lower_weight_le_seven_error (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) :=
  (lower_weight_le_sharp S depth i h a b).trans
    ((sharp_le_seven_activeX S depth i h a b).trans
      ((seven_activeX_le_seven_count S depth i h a b).trans
        (Nat.mul_le_mul_left 7 (active_count_le_weight S depth i h (a+b)))))

theorem weight_chain (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (N S depth i h a b).card ∧
      (N S depth i h a b).card ≤ (activeQ S depth i h (a+b)).card+
        ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card ∧
      (activeQ S depth i h (a+b)).card+∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card ≤
        (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card ∧
      (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card ≤
        7*((activeX S depth i h (a+b)).card+(activeQ S depth i h (a+b)).card) ∧
      7*((activeX S depth i h (a+b)).card+(activeQ S depth i h (a+b)).card) ≤ 7*HammingWeight (a+b) :=
  ⟨lower_weight_le_neighbors S depth i h a b,neighbors_card_le_sharp S depth i h a b,
    sharp_le_seven_activeX S depth i h a b,seven_activeX_le_seven_count S depth i h a b,
    Nat.mul_le_mul_left 7 (active_count_le_weight S depth i h (a+b))⟩

@[simp] theorem potential_self (a : Upper S depth i) : Phi S depth i h a a=0 :=
  BDL26RXFiniteBlockTransport.phi_self S depth i h _ a

@[simp] theorem remainder_self (a : Upper S depth i) : R S depth i h a a=0 :=
  BDL26RXFiniteBlockTransport.remainder_self S depth i h _ a

@[simp] theorem lower_self (a : Upper S depth i) : L S depth i h a a=0 :=
  BDL26RXFiniteBlockTransport.lower_self S depth i h _ a

/-- Complete unconditional construction; localization and numerical valence are derived internally. -/
theorem two_run (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val ∧
      HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) :=
  ⟨map1_with_potential S depth i h a b,lower_syndrome S depth i h a b,lower_weight_le_seven_error S depth i h a b⟩

theorem activeX_subset_of_support (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (E : Upper S depth i)
    (he : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h X0 ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h Q0) : activeX S depth i h E ⊆ X0 := by
  intro x hx
  obtain ⟨p,hpx,hn⟩ := (mem_activeX_iff S depth i h E x).mp hx
  rcases Finset.mem_union.mp (he ((support_mem E p).mpr hn)) with hp | hp
  · obtain ⟨y,hy,hpy⟩ := Finset.mem_biUnion.mp hp
    by_cases hxy : x=y
    · exact hxy.symm ▸ hy
    · exact False.elim ((Finset.disjoint_left.mp (x_regions_disjoint S depth i h x y hxy)) hpx hpy)
  · obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hp
    exact False.elim ((Finset.disjoint_left.mp (x_q_regions_disjoint S depth i h x q)) hpx hpq)

theorem activeQ_subset_of_support (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (E : Upper S depth i)
    (he : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h X0 ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h Q0) : activeQ S depth i h E ⊆ Q0 := by
  intro q hq
  obtain ⟨p,hpq,hn⟩ := (mem_activeQ_iff S depth i h E q).mp hq
  rcases Finset.mem_union.mp (he ((support_mem E p).mpr hn)) with hp | hp
  · obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hp
    exact False.elim ((Finset.disjoint_left.mp (x_q_regions_disjoint S depth i h x q)) hpx hpq)
  · obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp hp
    by_cases hqr : q=r
    · exact hqr.symm ▸ hr
    · exact False.elim ((Finset.disjoint_left.mp (q_regions_disjoint S depth i h q r hqr)) hpq hpr)

theorem active_sets_one_x (x : XCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLx S depth i h).correctionRegion x)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    activeX S depth i h E={x} ∧ activeQ S depth i h E=∅ := by
  have hs : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h {x} ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h ∅ := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,Finset.mem_singleton_self _,he hp⟩)
  exact ⟨Finset.Subset.antisymm (activeX_subset_of_support S depth i h {x} ∅ E hs)
      (Finset.singleton_subset_iff.mpr (active_x_of_restriction_ne_zero S depth i h E x hn)),
    Finset.subset_empty.mp (activeQ_subset_of_support S depth i h {x} ∅ E hs)⟩

theorem active_sets_one_q (q : QCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLq S depth i h).correctionRegion q)
    (hn : restrictWordLinear ((rxLq S depth i h).correctionRegion q) E≠0) :
    activeX S depth i h E=∅ ∧ activeQ S depth i h E={q} := by
  have hs : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h ∅ ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h {q} := by
    intro p hp
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,Finset.mem_singleton_self _,he hp⟩)
  exact ⟨Finset.subset_empty.mp (activeX_subset_of_support S depth i h ∅ {q} E hs),
    Finset.Subset.antisymm (activeQ_subset_of_support S depth i h ∅ {q} E hs)
      (Finset.singleton_subset_iff.mpr (active_q_of_restriction_ne_zero S depth i h E q hn))⟩

theorem gradient_pair_restriction_left (x0 x1 : XCoord S i) (hn : x0≠x1) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x0)
      (gradientError S depth i h x0+gradientError S depth i h x1)=boundaryGradient S depth i h x0 := by
  rw [map_add,gradientError_restriction,
    BDL26RXXStarTransport.error_other_x_zero S depth i h x1 x0 hn _
      (gradientError_supported S depth i h x1),add_zero]

theorem gradient_pair_restriction_right (x0 x1 : XCoord S i) (hn : x0≠x1) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x1)
      (gradientError S depth i h x0+gradientError S depth i h x1)=boundaryGradient S depth i h x1 := by
  rw [add_comm (gradientError S depth i h x0) (gradientError S depth i h x1)]
  exact gradient_pair_restriction_left S depth i h x1 x0 hn.symm

/-- The active labels of the genuine closed local gradients come from ERROR restrictions. -/
theorem gradient_pair_active (x0 x1 : XCoord S i) (hn : x0≠x1) :
    activeX S depth i h (gradientError S depth i h x0+gradientError S depth i h x1)={x0,x1} ∧
      activeQ S depth i h (gradientError S depth i h x0+gradientError S depth i h x1)=∅ := by
  let E := gradientError S depth i h x0+gradientError S depth i h x1
  have hs : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h {x0,x1} ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h ∅ := by
    have hs := BDL26RXFiniteBlockTransport.gradient_pair_localized S depth i h x0 x1 (0 : Upper S depth i)
    change hammingSupport ((0 : Upper S depth i)+(0+(gradientError S depth i h x0+gradientError S depth i h x1))) ⊆ _ at hs
    simpa only [zero_add] using hs
  have hm0 : x0 ∈ activeX S depth i h E :=
    active_x_of_restriction_ne_zero S depth i h E x0 (fun hz =>
      boundaryGradient_nonzero S depth i h x0 ((gradient_pair_restriction_left S depth i h x0 x1 hn).symm.trans hz))
  have hm1 : x1 ∈ activeX S depth i h E :=
    active_x_of_restriction_ne_zero S depth i h E x1 (fun hz =>
      boundaryGradient_nonzero S depth i h x1 ((gradient_pair_restriction_right S depth i h x0 x1 hn).symm.trans hz))
  have hi : {x0,x1} ⊆ activeX S depth i h E := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hm0
    · have he := Finset.mem_singleton.mp hy
      subst y
      exact hm1
  exact ⟨Finset.Subset.antisymm (activeX_subset_of_support S depth i h {x0,x1} ∅ E hs) hi,
    Finset.subset_empty.mp (activeQ_subset_of_support S depth i h {x0,x1} ∅ E hs)⟩

theorem error_shift (a E : Upper S depth i) : a+(a+E)=E := by
  rw [← add_assoc,word_add_self,zero_add]

theorem gradient_pair_shift_active (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    activeX S depth i h (a+b)={x0,x1} ∧ activeQ S depth i h (a+b)=∅ := by
  dsimp only
  rw [error_shift]
  exact gradient_pair_active S depth i h x0 x1 hn

theorem gradient_pair_potential_nonzero (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    Phi S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1))≠0 := by
  unfold Phi
  rw [(gradient_pair_shift_active S depth i h x0 x1 hn a).1]
  exact BDL26RXFiniteBlockTransport.gradient_pair_phi_nonzero S depth i h x0 x1 hn a

theorem gradient_pair_boundary_nonzero (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1)))≠0 := by
  unfold Phi
  rw [(gradient_pair_shift_active S depth i h x0 x1 hn a).1]
  exact BDL26RXFiniteBlockTransport.gradient_pair_boundary_nonzero S depth i h x0 x1 hn a

theorem gradient_pair_consumer (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    activeX S depth i h (a+b)={x0,x1} ∧ activeQ S depth i h (a+b)=∅ ∧
      Phi S depth i h a b≠0 ∧ (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b)≠0 ∧
      ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val ∧
      HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) := by
  dsimp only
  exact ⟨(gradient_pair_shift_active S depth i h x0 x1 hn a).1,
    (gradient_pair_shift_active S depth i h x0 x1 hn a).2,
    gradient_pair_potential_nonzero S depth i h x0 x1 hn a,
    gradient_pair_boundary_nonzero S depth i h x0 x1 hn a,
    map1_with_potential S depth i h _ _,lower_syndrome S depth i h _ _,lower_weight_le_seven_error S depth i h _ _⟩

/-- Exact Q-only active labels for two distinct actual lower basis labels and any original background. -/
theorem two_basis_shift_active (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 w
    activeX S depth i h (a+b)=∅ ∧ activeQ S depth i h (a+b)={q0,q1} := by
  dsimp only
  let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
  let E := a+(a+((indexedDecoderData S depth).selectedMap i).map1 w)
  have hs := BDL26RXFiniteBlockTransport.two_basis_shift_localized S depth i h q0 q1 a
  have hm : ∀ q ∈ ({q0,q1} : Finset (QCoord S i)), q ∈ activeQ S depth i h E := by
    intro q hq
    have hw : w q=1 := by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · simp [w,canonicalBasisWord,hn,Ne.symm hn]
      · have he := Finset.mem_singleton.mp hq
        subst q
        simp [w,canonicalBasisWord,hn,Ne.symm hn]
    apply (mem_activeQ_iff S depth i h E q).mpr
    refine ⟨(rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val,
      (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property,?_⟩
    have he : E=((indexedDecoderData S depth).selectedMap i).map1 w := error_shift S depth i _ _
    have hv := congrArg (fun e : Upper S depth i => e
      (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val) he
    have hr := BDL26RXFiniteBlockTransport.map1_at_cone S depth i h w q
    intro hz
    exact one_ne_zero ((hv.trans (hr.trans hw)).symm.trans hz)
  exact ⟨Finset.subset_empty.mp (activeX_subset_of_support S depth i h ∅ {q0,q1} E hs),
    Finset.Subset.antisymm (activeQ_subset_of_support S depth i h ∅ {q0,q1} E hs) hm⟩

theorem two_basis_shift_lower (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    L S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)=w := by
  dsimp only
  unfold L
  rw [(two_basis_shift_active S depth i h q0 q1 hn a).1]
  exact BDL26RXFiniteBlockTransport.lower_add_map1 S depth i h a _

theorem two_basis_shift_weight_le_two (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    HammingWeight (L S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)) ≤ 2 := by
  dsimp only
  have hw := lower_weight_le_sharp S depth i h a
    (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q0+canonicalBasisWord q1))
  rw [(two_basis_shift_active S depth i h q0 q1 hn a).1,
    (two_basis_shift_active S depth i h q0 q1 hn a).2] at hw
  simpa [hn,Ne.symm hn] using hw

open BDL26FiniteAlternatingCore

/-- Both original seed labels are extracted from the actual original ERROR difference. -/
theorem first_edge_cancellation_active (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    activeX S depth i (by rfl) (a+b)=∅ ∧
      activeQ S depth i (by rfl) (a+b)={(0 : BaseQubit),(4 : BaseQubit)} ∧
      L S depth i (by rfl) a b=BDL26RXFiniteBlockTransport.seedWord ∧
      HammingWeight (L S depth i (by rfl) a b) ≤ 2 ∧
      L S depth i (by rfl) a b≠0 ∧
      (coarseSum S depth i (by rfl) a b).val (0 : BaseZ)=0 ∧
      (coarseSum S depth i (by rfl) a b).val (1 : BaseZ)=1 ∧
      (coarseSum S depth i (by rfl) a b).val≠0 := by
  dsimp only
  have hn : (0 : BaseQubit)≠4 := by decide
  refine ⟨(two_basis_shift_active S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) hn a).1,
    (two_basis_shift_active S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) hn a).2,
    two_basis_shift_lower S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) hn a,
    two_basis_shift_weight_le_two S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) hn a,?_,
    (BDL26RXFiniteBlockTransport.first_edge_cancellation S depth hd a).2.2.2.2.1,
    (BDL26RXFiniteBlockTransport.first_edge_cancellation S depth hd a).2.2.2.2.2,
    BDL26RXFiniteBlockTransport.first_edge_cancellation_coarse_nonzero S depth hd a⟩
  intro hz
  exact BDL26RXFiniteBlockTransport.seedWord_nonzero
    ((two_basis_shift_lower S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) hn a).symm.trans hz)

theorem first_edge_cancellation_coarse_strict (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    hammingSupport (coarseSum S depth i (by rfl) a b).val≠NZ S depth i (by rfl) a b := by
  dsimp only
  have hx := (first_edge_cancellation_active S depth hd a).1
  have hq := (first_edge_cancellation_active S depth hd a).2.1
  have hnz := congrArg₂ (fun X Q => BDL26RXFiniteBlockTransport.neighborZ S depth ⟨0,hd⟩ X Q) hx hq
  intro he
  exact BDL26RXFiniteBlockTransport.first_edge_cancellation_support_strict S depth hd a (he.trans hnz)

theorem first_edge_cancellation_pair (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (copy : Fin 2) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((0 : BaseZ),copy)).val=0 ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((1 : BaseZ),copy)).val=1 :=
  BDL26RXFiniteBlockTransport.first_edge_cancellation_pair S depth hd a copy

theorem first_edge_cancellation_exterior (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (p : FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ)
    (hp : p ∉ (rxData S depth ⟨0,hd⟩ (by rfl)).zSector) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val p=0 :=
  BDL26RXFiniteBlockTransport.first_edge_cancellation_exterior S depth hd a p hp

/-- Partial cancellation also makes the actual upper image strictly smaller than the full neighbor image. -/
theorem first_edge_cancellation_image_strict (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val) ≠
      (NZ S depth i (by rfl) a b).biUnion (zPairImage (rxData S depth i (by rfl))) := by
  dsimp only
  have hbi {α β : Type} [DecidableEq α] [DecidableEq β]
      (Y : α → Finset β) (hdis : Set.PairwiseDisjoint (Set.univ : Set α) Y)
      (hne : ∀ z, (Y z).Nonempty) :
      Function.Injective (fun T : Finset α => T.biUnion Y) := by
    have hsub (V W : Finset α) (he : V.biUnion Y=W.biUnion Y) : V ⊆ W := by
      intro z hz
      obtain ⟨p,hp⟩ := hne z
      have hpW : p ∈ W.biUnion Y :=
        (congrArg (fun T : Finset β => p ∈ T) he).mp
          (Finset.mem_biUnion.mpr ⟨z,hz,hp⟩)
      obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hpW
      by_cases hzw : z=w
      · exact hzw.symm ▸ hw
      · exact False.elim ((Finset.disjoint_left.mp
          (hdis (Set.mem_univ z) (Set.mem_univ w) hzw)) hp hpw)
    intro V W he
    exact Finset.Subset.antisymm (hsub V W he) (hsub W V he.symm)
  let Y : ZCoord S ⟨0,hd⟩ →
      Finset (FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ) :=
    zPairImage (rxData S depth ⟨0,hd⟩ (by rfl))
  have hdis : Set.PairwiseDisjoint (Set.univ : Set (ZCoord S ⟨0,hd⟩)) Y :=
    zPairImage_pairwise_disjoint (rxData S depth ⟨0,hd⟩ (by rfl))
  have hne : ∀ z : ZCoord S ⟨0,hd⟩, (Y z).Nonempty := by
    intro z
    have hc : (Y z).card=2 := zPairImage_card (rxData S depth ⟨0,hd⟩ (by rfl)) z
    apply Finset.card_pos.mp
    rw [hc]
    decide
  have hinj : Function.Injective (fun T : Finset (ZCoord S ⟨0,hd⟩) => T.biUnion Y) :=
    hbi Y hdis hne
  intro he
  apply first_edge_cancellation_coarse_strict S depth hd a
  exact hinj ((selected_image_support_eq S depth ⟨0,hd⟩ (by rfl) a _).symm.trans he)

end QEC.Coding.BDL26RXActiveErrorTransport
