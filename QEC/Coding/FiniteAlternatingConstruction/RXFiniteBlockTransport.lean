import QEC.Coding.FiniteAlternatingConstruction.RXXStarTransport

/-!
# Canonical RX transport for finite original block sets

Project-derived internal refinement of BDL26 `paper.tex:3136–3185,3455–3481`,
with the actual coarse relation at `2325–2384`. All labels, original runs,
and both physical copies are retained. The sole localization assumption is
on the original error difference. This proves no parent-fibre confinement,
stopped-history stability, logical protection, or lifetime statement.
-/
noncomputable section
namespace QEC.Coding.BDL26RXFiniteBlockTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

def xBlocks (X0 : Finset (XCoord S i)) : Finset (FamilyQ S depth i.succ) :=
  X0.biUnion ((rxLx S depth i h).correctionRegion)

def qBlocks (Q0 : Finset (QCoord S i)) : Finset (FamilyQ S depth i.succ) :=
  Q0.biUnion ((rxLq S depth i h).correctionRegion)

/-- Original Q labels are retained, also for an empty X set. -/
def neighbors (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) : Finset (QCoord S i) :=
  Q0 ∪ X0.biUnion (incidentQ S depth i)

def star (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) :
    Finset (FamilyQ S depth i.succ) :=
  xBlocks S depth i h X0 ∪ qBlocks S depth i h (neighbors S depth i X0 Q0)

def degreeZeroBlocks (X0 : Finset (XCoord S i)) : Finset (FamilyX S depth i.succ) :=
  X0.biUnion (degreeZeroBlock S depth i h)

def neighborZ (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ neighbors S depth i X0 Q0,
    (state S i.val).presentation.qz q z=true

def Localized (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ xBlocks S depth i h X0 ∪ qBlocks S depth i h Q0

private theorem block_sum_at {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (J : Finset α) (Y : α → Finset β)
    (hd : ∀ r s, r≠s → Disjoint (Y r) (Y s)) (e : Word BDL26Field β)
    (r : α) (hr : r ∈ J) (p : β) (hp : p ∈ Y r) :
    (∑ s ∈ J, extendWordLinear (Y s) (restrictWordLinear (Y s) e)) p=e p := by
  rw [Finset.sum_apply,Finset.sum_eq_single r]
  · exact dif_pos hp
  · intro s _ hsr
    exact dif_neg (fun hs => (Finset.disjoint_left.mp (hd s r hsr)) hs hp)
  · simp [hr]

private theorem block_sum_zero {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (J : Finset α) (Y : α → Finset β) (e : Word BDL26Field β)
    (p : β) (hp : ∀ r ∈ J, p ∉ Y r) :
    (∑ r ∈ J, extendWordLinear (Y r) (restrictWordLinear (Y r) e)) p=0 := by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun r hr => dif_neg (hp r hr))

/-- Internal reconstruction from original labelled restrictions; no decomposition is supplied. -/
theorem error_decomposition (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    a+b = (∑ x ∈ X0, extendWordLinear ((rxLx S depth i h).correctionRegion x)
      (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (a+b))) +
      ∑ q ∈ Q0, extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (a+b)) := by
  funext p
  change (a+b) p = _ + _
  by_cases hx : ∃ x ∈ X0, p ∈ (rxLx S depth i h).correctionRegion x
  · obtain ⟨x,hx,hpx⟩ := hx
    rw [block_sum_at X0 _ (rxData S depth i h).cx_correction_regions_pairwise_disjoint
      (a+b) x hx p hpx]
    have hq : ∀ q ∈ Q0, p ∉ (rxLq S depth i h).correctionRegion q := by
      intro q _ hpq
      exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h x q)) hpx hpq
    rw [block_sum_zero Q0 _ (a+b) p hq,add_zero]
  · have hxp : ∀ x ∈ X0, p ∉ (rxLx S depth i h).correctionRegion x :=
      fun x hxx hpx => hx ⟨x,hxx,hpx⟩
    rw [block_sum_zero X0 _ (a+b) p hxp,zero_add]
    by_cases hq : ∃ q ∈ Q0, p ∈ (rxLq S depth i h).correctionRegion q
    · obtain ⟨q,hq,hpq⟩ := hq
      exact (block_sum_at Q0 _ (rxData S depth i h).cq_correction_regions_pairwise_disjoint
        (a+b) q hq p hpq).symm
    · have hqp : ∀ q ∈ Q0, p ∉ (rxLq S depth i h).correctionRegion q :=
        fun q hqq hpq => hq ⟨q,hqq,hpq⟩
      rw [block_sum_zero Q0 _ (a+b) p hqp]
      apply zero_off_support _ _ he p
      intro hm
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨x,hxx,hpx⟩ := Finset.mem_biUnion.mp hm
        exact hx ⟨x,hxx,hpx⟩
      · obtain ⟨q,hqq,hpq⟩ := Finset.mem_biUnion.mp hm
        exact hq ⟨q,hqq,hpq⟩

theorem error_other_x_zero (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (a+b)=0 := by
  funext p
  apply zero_off_support _ _ he p.val
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨x,hx,hpx⟩ := Finset.mem_biUnion.mp hp
    have hyx : y≠x := fun hh => hy (hh.symm ▸ hx)
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hyx)) p.property hpx
  · obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h y q)) p.property hpq

theorem input_other_x_agreement (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i b).val := by
  apply eq_of_word_add_zero
  have hz := (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global y (a+b)
  rw [error_other_x_zero S depth i h X0 Q0 y hy a b he,map_zero] at hz
  rw [actual_coboundary1 S depth] at hz
  simpa only [errorSyndrome,map_add] using hz

private theorem extended_supported (Y : Finset (FamilyQ S depth i.succ))
    (e : Upper S depth i) : hammingSupport (extendWordLinear Y (restrictWordLinear Y e)) ⊆ Y := by
  apply support_of_zero_off
  intro p hp
  exact dif_neg hp

theorem input_other_q_agreement (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (hq : q ∉ neighbors S depth i X0 Q0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i b).val := by
  have hxq : ∀ x ∈ X0, q ∉ incidentQ S depth i x := by
    intro x hx hi
    exact hq (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,hi⟩))
  have hqq : q ∉ Q0 := fun hm => hq (Finset.mem_union_left _ hm)
  have hz : restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((indexedFamily S depth).coboundary1 i.succ (a+b))=0 := by
    rw [error_decomposition S depth i h X0 Q0 a b he,map_add,map_add,map_sum,map_sum,map_sum,map_sum]
    have hx : (∑ x ∈ X0, restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        ((indexedFamily S depth).coboundary1 i.succ
          (extendWordLinear ((rxLx S depth i h).correctionRegion x)
            (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (a+b)))))=0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact x_error_nonincident_q_syndrome S depth i h x q (hxq x hx) _
        (extended_supported S depth i _ _)
    have hqz : (∑ r ∈ Q0, restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        ((indexedFamily S depth).coboundary1 i.succ
          (extendWordLinear ((rxLq S depth i h).correctionRegion r)
            (restrictWordLinear ((rxLq S depth i h).correctionRegion r) (a+b)))))=0 := by
      apply Finset.sum_eq_zero
      intro r hr
      let e := extendWordLinear ((rxLq S depth i h).correctionRegion r)
        (restrictWordLinear ((rxLq S depth i h).correctionRegion r) (a+b))
      have hs : hammingSupport e ⊆ (rxLq S depth i h).correctionRegion r :=
        extended_supported S depth i _ _
      have hk := (rxContract S depth i h).support_decomposition.cqDelta1_restriction_global q e
        (BDL26RXQBlockTransport.error_x_zero S depth i h r e hs)
      rw [BDL26RXQBlockTransport.error_other_q_zero S depth i h r e hs q
        (fun hh => hqq (hh.symm ▸ hr)),map_zero,actual_coboundary1 S depth] at hk
      exact hk
    rw [hx,hqz,zero_add]
  apply eq_of_word_add_zero
  simpa only [errorSyndrome,map_add] using hz

private theorem cx_eq_of_read (s t : (indexedFamily S depth).Cochain2 i.succ)
    (y : XCoord S i)
    (hy : restrictWordLinear ((rxLx S depth i h).syndromeRegion y) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y) t) :
    cxComponentTotal (rxData S depth i h) s y = cxComponentTotal (rxData S depth i h) t y := by
  have hx : rxXiSignal (rxData S depth i h) s (.inl y) 1 =
      rxXiSignal (rxData S depth i h) t (.inl y) 1 := by
    funext p
    rw [rxXiSignal_apply,rxXiSignal_apply]
    by_cases hd : (rxData S depth i h).levelGraph.graph.distance
        ((rxData S depth i h).topCenter p) (.inl y) ≤ ((1 : Nat) : WithTop Nat)
    · rw [if_pos hd,if_pos hd]
      have hc := BDL26RXQBlockTransport.incoming_one_x S depth i h y _
        (by simpa only [Nat.cast_one,WithTop.coe_one] using hd)
      exact congrFun hy ⟨p,((rxData S depth i h).topCenter_x_iff y p).mpr hc⟩
    · rw [if_neg hd,if_neg hd]
  calc
    _ = cxComponentTotal (rxData S depth i h) (rxXiSignal (rxData S depth i h) s (.inl y) 1) y :=
      rx_cx_component_invariant _ _ _
    _ = cxComponentTotal (rxData S depth i h) (rxXiSignal (rxData S depth i h) t (.inl y) 1) y := by rw [hx]
    _ = _ := (rx_cx_component_invariant _ _ _).symm

theorem canonical_other_cx_eq (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y :=
  cx_eq_of_read S depth i h _ _ y (input_other_x_agreement S depth i h X0 Q0 y hy a b he)

theorem canonical_other_cq_eq (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (hq : q ∉ neighbors S depth i X0 Q0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val q =
      cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val q := by
  have hxi : rxXiSignal (rxData S depth i h) (errorSyndrome S depth i a).val (.inr (.inl q)) 1 =
      rxXiSignal (rxData S depth i h) (errorSyndrome S depth i b).val (.inr (.inl q)) 1 := by
    funext p
    rw [rxXiSignal_apply,rxXiSignal_apply]
    by_cases hd : (rxData S depth i h).levelGraph.graph.distance
        ((rxData S depth i h).topCenter p) (.inr (.inl q)) ≤ ((1 : Nat) : WithTop Nat)
    · rw [if_pos hd,if_pos hd]
      rcases BDL26RXQBlockTransport.incoming_one_q S depth i h q _
          (by simpa only [Nat.cast_one,WithTop.coe_one] using hd) with hc | ⟨y,hc,hyq⟩
      · exact congrFun (input_other_q_agreement S depth i h X0 Q0 q hq a b he)
          ⟨p,((rxData S depth i h).topCenter_q_iff q p).mpr hc⟩
      · have hy : y ∉ X0 := by
          intro hy
          exact hq (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨y,hy,(mem_incidentQ S depth i y q).mpr hyq⟩))
        exact congrFun (input_other_x_agreement S depth i h X0 Q0 y hy a b he)
          ⟨p,((rxData S depth i h).topCenter_x_iff y p).mpr hc⟩
    · rw [if_neg hd,if_neg hd]
  calc
    _ = cqComponentTotal (rxData S depth i h)
        (rxXiSignal (rxData S depth i h) (errorSyndrome S depth i a).val (.inr (.inl q)) 1) q :=
      rx_q_component_invariant _ _ _
    _ = cqComponentTotal (rxData S depth i h)
        (rxXiSignal (rxData S depth i h) (errorSyndrome S depth i b).val (.inr (.inl q)) 1) q := by rw [hxi]
    _ = _ := (rx_q_component_invariant _ _ _).symm

theorem correction_difference_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star S depth i h X0 Q0 := by
  apply support_of_zero_off
  intro p hp
  have hx : ∀ y, cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y p =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y p := by
    intro y
    by_cases hy : y ∈ X0
    · have hp' : p ∉ (rxLx S depth i h).correctionRegion y := by
        intro hm
        exact hp (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨y,hy,hm⟩))
      rw [cxComponentTotal_supported _ _ _ _ hp',cxComponentTotal_supported _ _ _ _ hp']
    · exact congrFun (canonical_other_cx_eq S depth i h X0 Q0 y hy a b he) p
  have hq : ∀ q, cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val q p =
      cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val q p := by
    intro q
    by_cases hq : q ∈ neighbors S depth i X0 Q0
    · have hp' : p ∉ (rxLq S depth i h).correctionRegion q := by
        intro hm
        exact hp (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,hq,hm⟩))
      rw [cqComponentTotal_supported _ _ _ _ hp',cqComponentTotal_supported _ _ _ _ hp']
    · exact congrFun (canonical_other_cq_eq S depth i h X0 Q0 q hq a b he) p
  have hr : (run S depth i h a).correction p=(run S depth i h b).correction p := by
    simp only [run,rxStepOutput_correction_sum,Pi.add_apply,Finset.sum_apply]
    exact congrArg₂ (·+·) (Finset.sum_congr rfl (fun y _ => hx y))
      (Finset.sum_congr rfl (fun q _ => hq q))
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0
  rw [hr]
  exact CharTwo.add_self_eq_zero _

theorem input_supported_star (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (a+b) ⊆ star S depth i h X0 Q0 := by
  intro p hp
  rcases Finset.mem_union.mp (he hp) with hx | hq
  · exact Finset.mem_union_left _ hx
  · obtain ⟨q,hq,hpq⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q,Finset.mem_union_left _ hq,hpq⟩)

theorem updated_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (updated S depth i h a b) ⊆ star S depth i h X0 Q0 := by
  have he' := input_supported_star S depth i h X0 Q0 a b he
  have hc := correction_difference_supported S depth i h X0 Q0 a b he
  apply support_of_zero_off
  intro p hp
  have h1 := zero_off_support _ _ he' p hp
  have h2 := zero_off_support _ _ hc p hp
  change (a p+b p)+(run S depth i h a).correction p+(run S depth i h b).correction p=0
  change a p+b p=0 at h1
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0 at h2
  rw [h1,zero_add]
  exact h2

/-- Sum only the already fixed canonical component potentials of the same U. -/
def Phi (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Potential S depth i :=
  ∑ x ∈ X0, BDL26RXXStarTransport.potential S depth i h x a b

def R (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Upper S depth i :=
  updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)

theorem phi_supported (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 := by
  apply support_of_zero_off
  intro p hp
  rw [Phi,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply zero_off_support _ _ (potential_supported S depth i h x a b) p
  exact fun hm => hp (Finset.mem_biUnion.mpr ⟨x,hx,hm⟩)

theorem phi_boundary_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)) ⊆
      star S depth i h X0 Q0 := by
  apply support_of_zero_off
  intro p hp
  rw [Phi,map_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply zero_off_support _ _ (potential_boundary_supported S depth i h x a b) p
  intro hm
  rcases Finset.mem_union.mp hm with hpx | hpq
  · exact hp (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,hx,hpx⟩))
  · obtain ⟨q,hq,hpq⟩ := (mem_starQ S depth i h x p).mp hpq
    exact hp (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,hq⟩),hpq⟩))

theorem phi_boundary_cocycle (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b))=0 :=
  potential_cocycle S depth i _

theorem phi_boundary_x (X0 : Finset (XCoord S i)) (x : XCoord S i) (hx : x ∈ X0)
    (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by
  rw [Phi,map_sum,map_sum,Finset.sum_eq_single x]
  · exact potential_boundary_x S depth i h x a b
  · intro y _ hy
    exact potential_boundary_other_x S depth i h y x (Ne.symm hy) a b
  · simp [hx]

theorem phi_boundary_other_x (X0 : Finset (XCoord S i)) (x : XCoord S i) (hx : x ∉ X0)
    (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b))=0 := by
  rw [Phi,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro y hy
  exact potential_boundary_other_x S depth i h y x (fun hh => hx (hh.symm ▸ hy)) a b

theorem updated_other_x_zero (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (updated S depth i h a b)=0 := by
  funext p
  apply zero_off_support _ _ (updated_supported S depth i h X0 Q0 a b he) p.val
  intro hm
  rcases Finset.mem_union.mp hm with hpx | hpq
  · obtain ⟨x,hx,hpx⟩ := Finset.mem_biUnion.mp hpx
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x
        (fun hh => hy (hh.symm ▸ hx)))) p.property hpx
  · obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hpq
    exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h y q)) p.property hpq

/-- Every actual X ERROR restriction vanishes before the Cq argument. -/
theorem remainder_x_zero (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (R S depth i h X0 a b)=0 := by
  rw [R,map_add]
  by_cases hy : y ∈ X0
  · rw [phi_boundary_x S depth i h X0 y hy,word_add_self]
  · rw [updated_other_x_zero S depth i h X0 Q0 y hy a b he,
      phi_boundary_other_x S depth i h X0 y hy,zero_add]

theorem remainder_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (R S depth i h X0 a b) ⊆ qBlocks S depth i h (neighbors S depth i X0 Q0) := by
  have hs : hammingSupport (R S depth i h X0 a b) ⊆ star S depth i h X0 Q0 :=
    Finset.Subset.trans (hammingSupport_add_subset_union _ _)
      (Finset.union_subset (updated_supported S depth i h X0 Q0 a b he)
        (phi_boundary_supported S depth i h X0 Q0 a b))
  intro p hp
  rcases Finset.mem_union.mp (hs hp) with hpx | hpq
  · obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hpx
    have hz := congrFun (remainder_x_zero S depth i h X0 Q0 x a b he) ⟨p,hpx⟩
    exact False.elim ((show R S depth i h X0 a b p≠0 by simpa [hammingSupport] using hp) hz)
  · exact hpq

theorem remainder_delta (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (R S depth i h X0 a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [R,map_add,phi_boundary_cocycle,add_zero,updated_delta]

theorem remainder_q_kernel (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (R S depth i h X0 a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cqDelta1_restriction_global q
    (R S depth i h X0 a b) (fun y => remainder_x_zero S depth i h X0 Q0 y a b he)
  rw [actual_coboundary1 S depth,remainder_delta,map2_q_zero] at hk
  exact hk.symm

/-- Literal copy-zero cone root of the normalized complete updated error. -/
def L (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Lower S depth i :=
  fun q => R S depth i h X0 a b (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val

theorem remainder_q_constant (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    R S depth i h X0 a b (rxQVertexEquiv S depth i h q v).val = L S depth i h X0 a b q :=
  rxQ_kernel_constant S depth i h q _ (remainder_q_kernel S depth i h X0 Q0 q a b he) v

theorem lower_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (L S depth i h X0 a b) ⊆ neighbors S depth i X0 Q0 := by
  apply support_of_zero_off
  intro q hq
  apply zero_off_support _ _ (remainder_supported S depth i h X0 Q0 a b he)
  intro hp
  obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp hp
  have hrq : r=q := by
    by_contra hn
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hn))
      hpr (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property
  exact hq (hrq ▸ hr)

theorem map1_eq_remainder (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) = R S depth i h X0 a b := by
  rw [selected_rx,rxMap1_constant_Q S depth i h]
  funext p
  by_cases hp : p ∈ (rxData S depth i h).qCorrectionSector
  · rw [(rxData S depth i h).qCorrectionSector_eq_regions] at hp
    obtain ⟨q,_,hp⟩ := Finset.mem_biUnion.mp hp
    rw [Finset.sum_apply,Finset.sum_eq_single q]
    · change extendLocalSignal ((rxLq S depth i h).correctionRegion q)
        (fun _ => L S depth i h X0 a b q) p = _
      rw [extendLocalSignal,dif_pos hp]
      obtain ⟨v,hv⟩ := (rxQVertexEquiv S depth i h q).surjective ⟨p,hp⟩
      have hc := remainder_q_constant S depth i h X0 Q0 q a b he v
      rw [hv] at hc
      exact hc.symm
    · intro r _ hr
      exact dif_neg (fun hm => (Finset.disjoint_left.mp
        ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hr)) hm hp)
    · simp
  · rw [Finset.sum_apply]
    have hz : ∀ q, extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (fun _ => L S depth i h X0 a b q) p=0 := by
      intro q
      exact dif_neg (fun hm => hp (by
        rw [(rxData S depth i h).qCorrectionSector_eq_regions]
        exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hm⟩))
    rw [Finset.sum_eq_zero (fun q _ => hz q)]
    symm
    apply zero_off_support _ _ (remainder_supported S depth i h X0 Q0 a b he)
    intro hm
    obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hm
    exact hp (by
      rw [(rxData S depth i h).qCorrectionSector_eq_regions]
      exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hq⟩)

theorem map1_with_potential (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) =
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b) :=
  map1_eq_remainder S depth i h X0 Q0 a b he

theorem lower_syndrome (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
      (coarseSum S depth i h a b).val := by
  apply map2_injective S depth i h
  have hc := LinearMap.congr_fun (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (L S depth i h X0 a b)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b)) at hc
  rw [map1_eq_remainder S depth i h X0 Q0 a b he,remainder_delta] at hc
  exact hc.symm

theorem coarse_apply (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ neighbors S depth i X0 Q0, L S depth i h X0 a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by
  rw [← lower_syndrome S depth i h X0 Q0 a b he,indexedFamily_coboundary1]
  change (∑ q, L S depth i h X0 a b q *
    (if (state S i.val).presentation.qz q z=true then 1 else 0)) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  rw [zero_off_support _ _ (lower_supported S depth i h X0 Q0 a b he) q hq,zero_mul]

theorem coarse_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (coarseSum S depth i h a b).val ⊆ neighborZ S depth i X0 Q0 := by
  apply support_of_zero_off
  intro z hz
  rw [coarse_apply S depth i h X0 Q0 a b he z]
  apply Finset.sum_eq_zero
  intro q hq
  have hqz : (state S i.val).presentation.qz q z ≠ true := by
    intro hh
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨q,hq,hh⟩⟩)
  rw [if_neg hqz,mul_zero]

theorem selected_image_support_eq (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) =
      (hammingSupport (coarseSum S depth i h a b).val).biUnion (zPairImage (rxData S depth i h)) :=
  BDL26RXXStarTransport.selected_image_support_eq S depth i h a b

theorem selected_image_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆
      (neighborZ S depth i X0 Q0).biUnion (zPairImage (rxData S depth i h)) := by
  rw [selected_image_support_eq]
  intro p hp
  obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨z,coarse_supported S depth i h X0 Q0 a b he hz,hp⟩

theorem selected_image_pair (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val = (coarseSum S depth i h a b).val z :=
  BDL26RXXStarTransport.selected_image_pair S depth i h a b z copy

theorem selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 :=
  BDL26RXXStarTransport.selected_image_exterior S depth i h a b p hp

theorem lower_card_le (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (hammingSupport (L S depth i h X0 a b)).card ≤ (neighbors S depth i X0 Q0).card :=
  Finset.card_le_card (lower_supported S depth i h X0 Q0 a b he)

theorem neighbors_card_le (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) :
    (neighbors S depth i X0 Q0).card ≤ Q0.card + ∑ x ∈ X0, (incidentQ S depth i x).card := by
  have hb : (X0.biUnion (incidentQ S depth i)).card ≤ ∑ x ∈ X0, (incidentQ S depth i x).card := by
    induction X0 using Finset.induction_on with
    | empty => simp
    | @insert x X hx ih =>
      rw [Finset.biUnion_insert,Finset.sum_insert hx]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hb _)

@[simp] theorem phi_self (X0 : Finset (XCoord S i)) (a : Upper S depth i) : Phi S depth i h X0 a a=0 := by
  simp [Phi]

@[simp] theorem remainder_self (X0 : Finset (XCoord S i)) (a : Upper S depth i) : R S depth i h X0 a a=0 := by
  rw [R,updated_self,phi_self,map_zero,add_zero]

@[simp] theorem lower_self (X0 : Finset (XCoord S i)) (a : Upper S depth i) : L S depth i h X0 a a=0 := by
  unfold L
  rw [remainder_self]
  rfl

@[simp] theorem phi_empty (a b : Upper S depth i) : Phi S depth i h ∅ a b=0 := by simp [Phi]

@[simp] theorem neighbors_empty (Q0 : Finset (QCoord S i)) : neighbors S depth i ∅ Q0=Q0 := by
  simp [neighbors]

@[simp] theorem remainder_empty (a b : Upper S depth i) : R S depth i h ∅ a b=updated S depth i h a b := by
  rw [R,phi_empty,map_zero,add_zero]

theorem both_empty_error_zero (a b : Upper S depth i) (he : Localized S depth i h ∅ ∅ a b) : a+b=0 := by
  funext p
  apply zero_off_support _ _ he p
  simp [xBlocks,qBlocks]

@[simp] theorem phi_singleton (x : XCoord S i) (a b : Upper S depth i) :
    Phi S depth i h {x} a b=BDL26RXXStarTransport.potential S depth i h x a b := by simp [Phi]

@[simp] theorem remainder_singleton (x : XCoord S i) (a b : Upper S depth i) :
    R S depth i h {x} a b=BDL26RXXStarTransport.remainder S depth i h x a b := by
  rw [R,phi_singleton]
  rfl

@[simp] theorem lower_singleton_x (x : XCoord S i) (a b : Upper S depth i) :
    L S depth i h {x} a b=BDL26RXXStarTransport.lowerWord S depth i h x a b := by
  unfold L BDL26RXXStarTransport.lowerWord
  rw [remainder_singleton]

theorem lower_singleton_q (q : QCoord S i) (a b : Upper S depth i)
    (he : Localized S depth i h ∅ {q} a b) :
    L S depth i h ∅ a b=BDL26RXQBlockTransport.lowerWord S depth i h q a b := by
  have hs : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q := by
    simpa [Localized,xBlocks,qBlocks] using he
  funext r
  by_cases hr : r=q
  · subst r
    simp [L,remainder_empty,BDL26RXQBlockTransport.lowerWord,
      BDL26RXQBlockTransport.rootCoefficient,canonicalBasisWord]
  · have hn : r ∉ neighbors S depth i ∅ {q} := by simpa using hr
    have hz := zero_off_support _ _ (lower_supported S depth i h ∅ {q} a b he) r hn
    simpa [BDL26RXQBlockTransport.lowerWord,canonicalBasisWord,hr] using hz

/-- Full finite-set transport, with the internally fixed potential and literal root word. -/
theorem two_run (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 ∧
      hammingSupport (L S depth i h X0 a b) ⊆ neighbors S depth i X0 Q0 ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ neighborZ S depth i X0 Q0 :=
  ⟨map1_with_potential S depth i h X0 Q0 a b he,lower_syndrome S depth i h X0 Q0 a b he,
    phi_supported S depth i h X0 a b,lower_supported S depth i h X0 Q0 a b he,
    coarse_supported S depth i h X0 Q0 a b he⟩

private theorem correction_x_eq_of_cx_eq (x : XCoord S i) (a b : Upper S depth i)
    (hc : ∀ y, cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (run S depth i h a).correction =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (run S depth i h b).correction := by
  have hcx : (∑ y : XCoord S i,
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y) =
      ∑ y : XCoord S i, cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y :=
    Finset.sum_congr rfl (fun y _ => hc y)
  have hq : ∀ t : (indexedFamily S depth).Cochain2 i.succ,
      restrictWordLinear ((rxLx S depth i h).correctionRegion x)
        (∑ q : QCoord S i, cqComponentTotal (rxData S depth i h) t q)=0 := by
    intro t
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro q _
    funext p
    exact cqComponentTotal_supported _ _ _ _ (fun hp =>
      (Finset.disjoint_left.mp (x_q_disjoint S depth i h x q)) p.property hp)
  simp only [run,rxStepOutput_correction_sum,map_add]
  rw [hcx,hq,hq]

/-- Two distinct owners are kept as two original labels, even at a shared Q block. -/
theorem gradient_pair_localized (x0 x1 : XCoord S i) (a : Upper S depth i) :
    Localized S depth i h {x0,x1} ∅ a
      (a+(gradientError S depth i h x0+gradientError S depth i h x1)) := by
  change hammingSupport (a+(a+(_+_))) ⊆ _
  rw [← add_assoc,word_add_self,zero_add]
  intro p hp
  rcases Finset.mem_union.mp (hammingSupport_add_subset_union _ _ hp) with hp | hp
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨x0,by simp,gradientError_supported S depth i h x0 hp⟩)
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨x1,by simp,gradientError_supported S depth i h x1 hp⟩)

theorem gradient_pair_canonical_cx_eq (x0 x1 y : XCoord S i) (a : Upper S depth i) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h)
        (errorSyndrome S depth i (a+(gradientError S depth i h x0+gradientError S depth i h x1))).val y := by
  rw [← add_assoc]
  exact (gradient_canonical_cx_eq S depth i h x0 y a).trans
    (gradient_canonical_cx_eq S depth i h x1 y (a+gradientError S depth i h x0))

theorem gradient_pair_updated_x_left (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x0)
      (updated S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1))) =
      boundaryGradient S depth i h x0 := by
  have hr := correction_x_eq_of_cx_eq S depth i h x0 a
    (a+(gradientError S depth i h x0+gradientError S depth i h x1))
    (fun y => gradient_pair_canonical_cx_eq S depth i h x0 x1 y a)
  have ha : a+(a+(gradientError S depth i h x0+gradientError S depth i h x1)) =
      gradientError S depth i h x0+gradientError S depth i h x1 := by
    rw [← add_assoc,word_add_self,zero_add]
  rw [updated,ha,map_add,map_add,hr,add_assoc,word_add_self,add_zero,map_add,
    gradientError_restriction,
    BDL26RXXStarTransport.error_other_x_zero S depth i h x1 x0 hne _
      (gradientError_supported S depth i h x1),add_zero]

theorem gradient_pair_updated_x_right (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x1)
      (updated S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1))) =
      boundaryGradient S depth i h x1 := by
  rw [add_comm (gradientError S depth i h x0) (gradientError S depth i h x1)]
  exact gradient_pair_updated_x_left S depth i h x1 x0 hne.symm a

theorem gradient_pair_boundary_nonzero (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h {x0,x1} a
        (a+(gradientError S depth i h x0+gradientError S depth i h x1))) ≠ 0 := by
  intro hz
  have he := phi_boundary_x S depth i h {x0,x1} x0 (by simp) a
    (a+(gradientError S depth i h x0+gradientError S depth i h x1))
  rw [hz,map_zero,gradient_pair_updated_x_left S depth i h x0 x1 hne a] at he
  exact boundaryGradient_nonzero S depth i h x0 he.symm

theorem gradient_pair_phi_nonzero (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    Phi S depth i h {x0,x1} a
      (a+(gradientError S depth i h x0+gradientError S depth i h x1)) ≠ 0 := by
  intro hz
  apply gradient_pair_boundary_nonzero S depth i h x0 x1 hne a
  rw [hz,map_zero]

/-- Overlap consumer with arbitrary original background and complete original runs. -/
theorem gradient_pair_consumer (x0 x1 : XCoord S i) (hne : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    Localized S depth i h {x0,x1} ∅ a b ∧
      restrictWordLinear ((rxLx S depth i h).correctionRegion x0) (updated S depth i h a b) =
        boundaryGradient S depth i h x0 ∧
      restrictWordLinear ((rxLx S depth i h).correctionRegion x1) (updated S depth i h a b) =
        boundaryGradient S depth i h x1 ∧
      Phi S depth i h {x0,x1} a b≠0 ∧
      (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h {x0,x1} a b)≠0 ∧
      ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h {x0,x1} a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h {x0,x1} a b) := by
  dsimp only
  exact ⟨gradient_pair_localized S depth i h x0 x1 a,
    gradient_pair_updated_x_left S depth i h x0 x1 hne a,
    gradient_pair_updated_x_right S depth i h x0 x1 hne a,
    gradient_pair_phi_nonzero S depth i h x0 x1 hne a,
    gradient_pair_boundary_nonzero S depth i h x0 x1 hne a,
    map1_with_potential S depth i h {x0,x1} ∅ _ _ (gradient_pair_localized S depth i h x0 x1 a)⟩

theorem map1_at_cone (w : Lower S depth i) (q : QCoord S i) :
    ((indexedDecoderData S depth).selectedMap i).map1 w
      (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val = w q := by
  rw [selected_rx,rxMap1_constant_Q S depth i h,Finset.sum_apply,Finset.sum_eq_single q]
  · change extendLocalSignal ((rxLq S depth i h).correctionRegion q) (fun _ => w q)
        (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val = w q
    exact dif_pos (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property
  · intro r _ hr
    exact dif_neg (fun hp => (Finset.disjoint_left.mp
      ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hr)) hp
      (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property)
  · simp

/-- Actual map1-shift invariance fixes the literal lower word for every w. -/
theorem lower_add_map1 (a : Upper S depth i) (w : Lower S depth i) :
    L S depth i h ∅ a (a+((indexedDecoderData S depth).selectedMap i).map1 w)=w := by
  funext q
  change R S depth i h ∅ a (a+((indexedDecoderData S depth).selectedMap i).map1 w) _=w q
  rw [remainder_empty,BDL26RXQBlockTransport.updated_add_map1,map1_at_cone]

theorem two_basis_shift_localized (q0 q1 : QCoord S i) (a : Upper S depth i) :
    Localized S depth i h ∅ {q0,q1} a
      (a+((indexedDecoderData S depth).selectedMap i).map1
        (canonicalBasisWord q0+canonicalBasisWord q1)) := by
  change hammingSupport (a+(a+_)) ⊆ _
  rw [← add_assoc,word_add_self,zero_add,map_add]
  intro p hp
  rcases Finset.mem_union.mp (hammingSupport_add_subset_union _ _ hp) with hp | hp
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q0,by simp,BDL26RXQBlockTransport.map1_basis_supported S depth i h q0 hp⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q1,by simp,BDL26RXQBlockTransport.map1_basis_supported S depth i h q1 hp⟩)

open BDL26FiniteAlternatingCore

/-- The real seed overlap: Q label four is incident to both distinct X owners. -/
theorem first_edge_shared_q (S : OddScale) (depth : Nat) (hd : 0<depth) :
    let i : StepIndex depth := ⟨0,hd⟩
    (0 : BaseX)≠1 ∧
      (4 : BaseQubit) ∈ incidentQ S depth i (0 : BaseX) ∧
      (4 : BaseQubit) ∈ incidentQ S depth i (1 : BaseX) := by
  dsimp only
  refine ⟨by decide,?_,?_⟩
  · apply (mem_incidentQ S depth ⟨0,hd⟩ (0 : BaseX) (4 : BaseQubit)).mpr
    change baseTannerSquarePresentation.xq (0 : BaseX) (4 : BaseQubit)=true
    decide
  · apply (mem_incidentQ S depth ⟨0,hd⟩ (1 : BaseX) (4 : BaseQubit)).mpr
    change baseTannerSquarePresentation.xq (1 : BaseX) (4 : BaseQubit)=true
    decide

def seedWord : Word BDL26Field BaseQubit := canonicalBasisWord (0 : BaseQubit)+canonicalBasisWord (4 : BaseQubit)

theorem seedWord_nonzero : seedWord≠0 := by
  intro hz
  have hh := congrFun hz (0 : BaseQubit)
  simpa [seedWord,canonicalBasisWord] using hh

theorem seedWord_syndrome_zero : tannerCoboundary1 baseTannerSquarePresentation seedWord (0 : BaseZ)=0 := by
  let q0 : baseTannerSquarePresentation.Q := (0 : BaseQubit)
  let q4 : baseTannerSquarePresentation.Q := (4 : BaseQubit)
  let z0 : baseTannerSquarePresentation.Z := (0 : BaseZ)
  change tannerCoboundary1 baseTannerSquarePresentation
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0+
      canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)
    z0=(0 : BDL26RZMap1CoordinateBridge.Field)
  have hm := congrFun ((tannerCoboundary1 baseTannerSquarePresentation).map_add
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0)
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)) z0
  have h0 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q0 z0
  have h4 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q4 z0
  exact hm.trans ((congrArg₂ (fun a b : BDL26RZMap1CoordinateBridge.Field => a+b) h0 h4).trans
    (by decide))

theorem seedWord_syndrome_one : tannerCoboundary1 baseTannerSquarePresentation seedWord (1 : BaseZ)=1 := by
  let q0 : baseTannerSquarePresentation.Q := (0 : BaseQubit)
  let q4 : baseTannerSquarePresentation.Q := (4 : BaseQubit)
  let z1 : baseTannerSquarePresentation.Z := (1 : BaseZ)
  change tannerCoboundary1 baseTannerSquarePresentation
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0+
      canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)
    z1=(1 : BDL26RZMap1CoordinateBridge.Field)
  have hm := congrFun ((tannerCoboundary1 baseTannerSquarePresentation).map_add
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0)
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)) z1
  have h0 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q0 z1
  have h4 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q4 z1
  exact hm.trans ((congrArg₂ (fun a b : BDL26RZMap1CoordinateBridge.Field => a+b) h0 h4).trans
    (by decide))

/-- Concrete partial cancellation, with nonzero true lower/coarse words and both original corrections. -/
theorem first_edge_cancellation (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    Localized S depth i (by rfl) ∅ {(0 : BaseQubit),(4 : BaseQubit)} a b ∧
      L S depth i (by rfl) ∅ a b=seedWord ∧
      L S depth i (by rfl) ∅ a b≠0 ∧
      (run S depth i (by rfl) b).correction=(run S depth i (by rfl) a).correction ∧
      (coarseSum S depth i (by rfl) a b).val (0 : BaseZ)=0 ∧
      (coarseSum S depth i (by rfl) a b).val (1 : BaseZ)=1 := by
  dsimp only
  refine ⟨two_basis_shift_localized S depth ⟨0,hd⟩ (by rfl) (0 : BaseQubit) (4 : BaseQubit) a,
    lower_add_map1 S depth ⟨0,hd⟩ (by rfl) a seedWord,?_,
    BDL26RXQBlockTransport.correction_add_map1_eq S depth ⟨0,hd⟩ (by rfl) a seedWord,?_,?_⟩
  · intro hz
    exact seedWord_nonzero ((lower_add_map1 S depth ⟨0,hd⟩ (by rfl) a seedWord).symm.trans hz)
  · have hc := congrFun (BDL26RXQBlockTransport.coarse_add_map1 S depth ⟨0,hd⟩ (by rfl) a seedWord) (0 : BaseZ)
    have ht := congrFun (LinearMap.congr_fun
      (indexedFamily_coboundary1 S depth (⟨0,hd⟩ : StepIndex depth).castSucc) seedWord) (0 : BaseZ)
    exact hc.trans (ht.trans seedWord_syndrome_zero)
  · have hc := congrFun (BDL26RXQBlockTransport.coarse_add_map1 S depth ⟨0,hd⟩ (by rfl) a seedWord) (1 : BaseZ)
    have ht := congrFun (LinearMap.congr_fun
      (indexedFamily_coboundary1 S depth (⟨0,hd⟩ : StepIndex depth).castSucc) seedWord) (1 : BaseZ)
    exact hc.trans (ht.trans seedWord_syndrome_one)

theorem first_edge_cancellation_pair (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (copy : Fin 2) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((0 : BaseZ),copy)).val=0 ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((1 : BaseZ),copy)).val=1 := by
  dsimp only
  exact ⟨(selected_image_pair S depth ⟨0,hd⟩ (by rfl) a
      (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord) (0 : BaseZ) copy).trans
        (first_edge_cancellation S depth hd a).2.2.2.2.1,
    (selected_image_pair S depth ⟨0,hd⟩ (by rfl) a
      (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord) (1 : BaseZ) copy).trans
        (first_edge_cancellation S depth hd a).2.2.2.2.2⟩

/-- The uncancelled Z-one coefficient certifies a nonzero actual coarse word. -/
theorem first_edge_cancellation_coarse_nonzero (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    (coarseSum S depth i (by rfl) a b).val≠0 := by
  dsimp only
  intro hz
  have hh := congrFun hz (1 : BaseZ)
  have hw := (first_edge_cancellation S depth hd a).2.2.2.2.2
  exact one_ne_zero (hw.symm.trans hh)

/-- Cancellation leaves the actual selected image zero on every exterior coordinate. -/
theorem first_edge_cancellation_exterior (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (p : FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ)
    (hp : p ∉ (rxData S depth ⟨0,hd⟩ (by rfl)).zSector) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val p=0 := by
  dsimp only
  exact selected_image_exterior S depth ⟨0,hd⟩ (by rfl) a
    (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord) p hp

theorem first_edge_cancellation_support_strict (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    hammingSupport (coarseSum S depth i (by rfl) a b).val ≠
      neighborZ S depth i ∅ {(0 : BaseQubit),(4 : BaseQubit)} := by
  dsimp only
  intro he
  have hm : (0 : BaseZ) ∈ neighborZ S depth ⟨0,hd⟩ ∅ {(0 : BaseQubit),(4 : BaseQubit)} := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(0 : BaseQubit),?_,?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    · change baseTannerSquarePresentation.qz (0 : BaseQubit) (0 : BaseZ)=true
      decide
  have hs : (0 : BaseZ) ∈ hammingSupport (coarseSum S depth ⟨0,hd⟩ (by rfl) a
      (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord)).val := he.symm ▸ hm
  have hn : (coarseSum S depth ⟨0,hd⟩ (by rfl) a
      (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord)).val (0 : BaseZ)≠0 := by
    let tau := (coarseSum S depth ⟨0,hd⟩ (by rfl) a
      (a+((indexedDecoderData S depth).selectedMap ⟨0,hd⟩).map1 seedWord)).val
    exact ((@Finset.mem_filter _ (fun z => tau z≠0)
      (fun z => @instDecidableNot (tau z=0) (ZMod.decidableEq 2 (tau z) 0)) _ _).mp hs).2
  exact hn (first_edge_cancellation S depth hd a).2.2.2.2.1

end QEC.Coding.BDL26RXFiniteBlockTransport
