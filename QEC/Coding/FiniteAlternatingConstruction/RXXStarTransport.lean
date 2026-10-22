import QEC.Coding.FiniteAlternatingConstruction.RXXStarTransport.Geometry

/-!
# Canonical RX transport of one actual X error block

BDL26 `paper.tex:3136–3185,3455–3481`. This internal finite lemma first
constructs and lifts an actual local Cx potential, then applies the staged
Cq restriction to the resulting zero-X error. Neither the original selectors
nor the arbitrary upper backgrounds are replaced. No parent-fibre, stability,
or logical-protection conclusion is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26RXXStarTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

/-- Only the original input-error support is assumed. -/
def OneX (x : XCoord S i) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ (rxLx S depth i h).correctionRegion x

theorem input_other_x_agreement (x y : XCoord S i) (hy : y≠x)
    (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i b).val := by
  apply eq_of_word_add_zero
  have hz := (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global y (a+b)
  rw [error_other_x_zero S depth i h x y hy (a+b) he, map_zero] at hz
  rw [actual_coboundary1 S depth] at hz
  simpa only [errorSyndrome,map_add] using hz

theorem input_nonincident_q_agreement (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i b).val := by
  apply eq_of_word_add_zero
  have hz := x_error_nonincident_q_syndrome S depth i h x q hq (a+b) he
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

theorem canonical_other_cx_eq (x y : XCoord S i) (hy : y≠x)
    (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y :=
  cx_eq_of_read S depth i h _ _ y (input_other_x_agreement S depth i h x y hy a b he)

theorem canonical_nonincident_cq_eq (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
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
      · exact congrFun (input_nonincident_q_agreement S depth i h x q hq a b he)
          ⟨p,((rxData S depth i h).topCenter_q_iff q p).mpr hc⟩
      · have hy : y≠x := by
          intro hh
          subst y
          exact hq ((mem_incidentQ S depth i x q).mpr hyq)
        exact congrFun (input_other_x_agreement S depth i h x y hy a b he)
          ⟨p,((rxData S depth i h).topCenter_x_iff y p).mpr hc⟩
    · rw [if_neg hd,if_neg hd]
  calc
    _ = cqComponentTotal (rxData S depth i h)
        (rxXiSignal (rxData S depth i h) (errorSyndrome S depth i a).val (.inr (.inl q)) 1) q :=
      rx_q_component_invariant _ _ _
    _ = cqComponentTotal (rxData S depth i h)
        (rxXiSignal (rxData S depth i h) (errorSyndrome S depth i b).val (.inr (.inl q)) 1) q := by rw [hxi]
    _ = _ := (rx_q_component_invariant _ _ _).symm

/-- Cancel every component of the same original canonical correction outside the star. -/
theorem correction_difference_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h x := by
  apply support_of_zero_off
  intro p hp
  have hx : ∀ y, cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y p =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y p := by
    intro y
    by_cases hy : y=x
    · subst y
      have hp' : p ∉ (rxLx S depth i h).correctionRegion x :=
        fun hm => hp (Finset.mem_union_left _ hm)
      rw [cxComponentTotal_supported _ _ _ _ hp',cxComponentTotal_supported _ _ _ _ hp']
    · exact congrFun (canonical_other_cx_eq S depth i h x y hy a b he) p
  have hq : ∀ q, cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val q p =
      cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val q p := by
    intro q
    by_cases hq : q ∈ incidentQ S depth i x
    · have hp' : p ∉ (rxLq S depth i h).correctionRegion q := by
        intro hm
        exact hp (Finset.mem_union_right _ ((mem_starQ S depth i h x p).mpr ⟨q,hq,hm⟩))
      rw [cqComponentTotal_supported _ _ _ _ hp',cqComponentTotal_supported _ _ _ _ hp']
    · exact congrFun (canonical_nonincident_cq_eq S depth i h x q hq a b he) p
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0
  have hr : (run S depth i h a).correction p=(run S depth i h b).correction p := by
    simp only [run,rxStepOutput_correction_sum,Pi.add_apply,Finset.sum_apply]
    exact congrArg₂ (·+·) (Finset.sum_congr rfl (fun y _ => hx y))
      (Finset.sum_congr rfl (fun q _ => hq q))
  rw [hr]
  exact CharTwo.add_self_eq_zero _

theorem updated_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (updated S depth i h a b) ⊆ star1 S depth i h x := by
  apply support_of_zero_off
  intro p hp
  have h1 := zero_off_support (a+b) _ he p (fun hm => hp (Finset.mem_union_left _ hm))
  have h2 := zero_off_support _ _ (correction_difference_supported S depth i h x a b he) p hp
  change a p+b p=0 at h1
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0 at h2
  change (a p+b p)+(run S depth i h a).correction p+(run S depth i h b).correction p=0
  rw [h1,zero_add]
  exact h2

/-- The local X cycle follows from the actual full updated syndrome, without a support premise. -/
theorem updated_x_kernel (x : XCoord S i) (a b : Upper S depth i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta1 x
      (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global x
    (updated S depth i h a b)
  rw [actual_coboundary1 S depth,updated_delta,map2_x_zero] at hk
  exact hk.symm

theorem localPotential_exists (x : XCoord S i) (a b : Upper S depth i) :
    ∃ s : LocalPotential S i x, (rxContract S depth i h).rx_local_complexes.cxDelta0 x s =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by
  have hk := updated_x_kernel S depth i h x a b
  change _ ∈ LinearMap.ker ((rxContract S depth i h).rx_local_complexes.cxDelta1 x) at hk
  rw [(rxContract S depth i h).rx_local_cohomology.cx_h1_ker_eq_range x] at hk
  exact hk

/-- The explicit zero branch fixes the self case without any assumption on the decoder at zero. -/
def localPotential (x : XCoord S i) (a b : Upper S depth i) : LocalPotential S i x :=
  if restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b)=0 then 0
  else Classical.choose (localPotential_exists S depth i h x a b)

theorem localPotential_boundary (x : XCoord S i) (a b : Upper S depth i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta0 x (localPotential S depth i h x a b) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by
  unfold localPotential
  split_ifs with hz
  · rw [map_zero,hz]
  · exact Classical.choose_spec (localPotential_exists S depth i h x a b)

def potential (x : XCoord S i) (a b : Upper S depth i) : Potential S depth i :=
  (rxContract S depth i h).support_decomposition.cxLift0 x (localPotential S depth i h x a b)

def remainder (x : XCoord S i) (a b : Upper S depth i) : Upper S depth i :=
  updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ
    (potential S depth i h x a b)

theorem potential_supported (x : XCoord S i) (a b : Upper S depth i) :
    hammingSupport (potential S depth i h x a b) ⊆ degreeZeroBlock S depth i h x :=
  lift_supported S depth i h x _

theorem potential_boundary_supported (x : XCoord S i) (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b)) ⊆
      star1 S depth i h x := lift_boundary_supported S depth i h x _

theorem potential_boundary_x (x : XCoord S i) (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b)) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) :=
  ((rxContract S depth i h).support_decomposition.cxDelta0_restriction x _).trans
    (localPotential_boundary S depth i h x a b)

theorem potential_boundary_other_x (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y)
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b))=0 :=
  rxXLift_boundary_other_x S depth i h x y hy _

theorem potential_boundary_cocycle (x : XCoord S i) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b))=0 :=
  potential_cocycle S depth i _

theorem updated_other_x_zero (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (updated S depth i h a b)=0 := by
  funext p
  apply zero_off_support _ _ (updated_supported S depth i h x a b he) p.val
  intro hp
  rcases Finset.mem_union.mp hp with hpx | hpq
  · exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hy)) p.property hpx
  · obtain ⟨q,_,hq⟩ := (mem_starQ S depth i h x p.val).mp hpq
    exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h y q)) p.property hq

/-- This zero-X ERROR statement is established before any staged Q argument. -/
theorem remainder_x_zero (x y : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (remainder S depth i h x a b)=0 := by
  rw [remainder,map_add]
  by_cases hy : y=x
  · subst y
    rw [potential_boundary_x,word_add_self]
  · rw [updated_other_x_zero S depth i h x y hy a b he,
      potential_boundary_other_x S depth i h x y hy,zero_add]

theorem remainder_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (remainder S depth i h x a b) ⊆ starQ S depth i h x := by
  have hs : hammingSupport (remainder S depth i h x a b) ⊆ star1 S depth i h x :=
    Finset.Subset.trans (hammingSupport_add_subset_union _ _)
      (Finset.union_subset (updated_supported S depth i h x a b he)
        (potential_boundary_supported S depth i h x a b))
  intro p hp
  rcases Finset.mem_union.mp (hs hp) with hpx | hpq
  · have hz := congrFun (remainder_x_zero S depth i h x x a b he) ⟨p,hpx⟩
    exact False.elim ((show remainder S depth i h x a b p≠0 by simpa [hammingSupport] using hp) hz)
  · exact hpq

theorem remainder_delta (x : XCoord S i) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (remainder S depth i h x a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [remainder,map_add,potential_boundary_cocycle,add_zero,updated_delta]

/-- Now the original staged Cq formula applies, with zero X errors proved above. -/
theorem remainder_q_kernel (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (remainder S depth i h x a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cqDelta1_restriction_global q
    (remainder S depth i h x a b) (fun y => remainder_x_zero S depth i h x y a b he)
  rw [actual_coboundary1 S depth,remainder_delta,map2_q_zero] at hk
  exact hk.symm

/-- Every lower coordinate is literally evaluated at its actual copy-zero cone root. -/
def lowerWord (x : XCoord S i) (a b : Upper S depth i) : Lower S depth i :=
  fun q => remainder S depth i h x a b
    (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val

theorem remainder_q_constant (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    remainder S depth i h x a b (rxQVertexEquiv S depth i h q v).val =
      lowerWord S depth i h x a b q :=
  rxQ_kernel_constant S depth i h q _ (remainder_q_kernel S depth i h x q a b he) v

theorem lower_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (lowerWord S depth i h x a b) ⊆ incidentQ S depth i x := by
  apply support_of_zero_off
  intro q hq
  apply zero_off_support _ _ (remainder_supported S depth i h x a b he)
  intro hp
  obtain ⟨r,hr,hpr⟩ := (mem_starQ S depth i h x _).mp hp
  have hrq : r=q := by
    by_contra hn
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hn))
      hpr (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property
  exact hq (hrq ▸ hr)

/-- Full selected map1, not only its restriction to the Q sector. -/
theorem map1_eq_remainder (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
      remainder S depth i h x a b := by
  rw [selected_rx,rxMap1_constant_Q S depth i h]
  funext p
  by_cases hp : p ∈ (rxData S depth i h).qCorrectionSector
  · rw [(rxData S depth i h).qCorrectionSector_eq_regions] at hp
    obtain ⟨q,_,hp⟩ := Finset.mem_biUnion.mp hp
    rw [Finset.sum_apply,Finset.sum_eq_single q]
    · change extendLocalSignal ((rxLq S depth i h).correctionRegion q)
        (fun _ => lowerWord S depth i h x a b q) p = _
      rw [extendLocalSignal,dif_pos hp]
      obtain ⟨v,hv⟩ := (rxQVertexEquiv S depth i h q).surjective ⟨p,hp⟩
      have hc := remainder_q_constant S depth i h x q a b he v
      rw [hv] at hc
      exact hc.symm
    · intro r _ hr
      exact dif_neg (fun hm => (Finset.disjoint_left.mp
        ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hr)) hm hp)
    · simp
  · rw [Finset.sum_apply]
    have hz : ∀ q, extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (fun _ => lowerWord S depth i h x a b q) p=0 := by
      intro q
      exact dif_neg (fun hm => hp (by
        rw [(rxData S depth i h).qCorrectionSector_eq_regions]
        exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hm⟩))
    rw [Finset.sum_eq_zero (fun q _ => hz q)]
    symm
    apply zero_off_support _ _ (remainder_supported S depth i h x a b he)
    intro hm
    obtain ⟨q,_,hq⟩ := (mem_starQ S depth i h x p).mp hm
    exact hp (by
      rw [(rxData S depth i h).qCorrectionSector_eq_regions]
      exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hq⟩)

theorem map1_with_potential (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ
        (potential S depth i h x a b) := map1_eq_remainder S depth i h x a b he

theorem map2_injective (h : i.val % 2=0) :
    Function.Injective ((indexedDecoderData S depth).selectedMap i).map2 := by
  intro u v huv
  rw [selected_rx] at huv
  funext z
  have he := congrFun huv ((rxData S depth i h).induced.zPairEquiv (z,0)).val
  simpa only [(rxData S depth i h).induced.map2_diagonal] using he

theorem lower_syndrome (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
      (coarseSum S depth i h a b).val := by
  apply map2_injective S depth i h
  have hc := LinearMap.congr_fun (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (lowerWord S depth i h x a b)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b)) at hc
  rw [map1_eq_remainder S depth i h x a b he,remainder_delta] at hc
  exact hc.symm

/-- The original labelled F₂ sum retains all incident labels and cancellation. -/
theorem coarse_apply (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ incidentQ S depth i x, lowerWord S depth i h x a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by
  rw [← lower_syndrome S depth i h x a b he,indexedFamily_coboundary1]
  change (∑ q, lowerWord S depth i h x a b q *
    (if (state S i.val).presentation.qz q z=true then 1 else 0)) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  rw [zero_off_support _ _ (lower_supported S depth i h x a b he) q hq,zero_mul]

theorem coarse_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x := by
  apply support_of_zero_off
  intro z hz
  rw [coarse_apply S depth i h x a b he z]
  apply Finset.sum_eq_zero
  intro q hq
  have hqz : (state S i.val).presentation.qz q z ≠ true := by
    intro hh
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨q,hq,hh⟩⟩)
  rw [if_neg hqz,mul_zero]

def twoCopyImage (Y : Finset (ZCoord S i)) : Finset (FamilyZ S depth i.succ) :=
  Y.biUnion (zPairImage (rxData S depth i h))

theorem selected_image_support_eq (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) =
      twoCopyImage S depth i h (hammingSupport (coarseSum S depth i h a b).val) := by
  rw [selected_rx]
  exact map2_support_eq_biUnion (rxData S depth i h) (coarseSum S depth i h a b).val

theorem selected_image_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆ twoCopyImage S depth i h (incidentZ S depth i x) := by
  rw [selected_image_support_eq]
  intro p hp
  obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨z,coarse_supported S depth i h x a b he hz,hp⟩

theorem selected_image_pair (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val = (coarseSum S depth i h a b).val z := by
  rw [selected_rx]
  exact (rxData S depth i h).induced.map2_diagonal _ _ _

theorem selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 := by
  rw [selected_rx]
  exact (rxData S depth i h).induced.map2_auxiliary_zero _ p
    (by simpa only [← (rxData S depth i h).zSector_eq_induced] using hp)

/-- The explicit self branch, retaining both original decoder corrections. -/
theorem updated_self (a : Upper S depth i) : updated S depth i h a a=0 := by
  unfold updated
  rw [word_add_self,zero_add,word_add_self]

@[simp] theorem localPotential_self (x : XCoord S i) (a : Upper S depth i) :
    localPotential S depth i h x a a=0 := by
  simp [localPotential,updated_self]

@[simp] theorem potential_self (x : XCoord S i) (a : Upper S depth i) :
    potential S depth i h x a a=0 := by
  rw [potential,localPotential_self,map_zero]

@[simp] theorem remainder_self (x : XCoord S i) (a : Upper S depth i) :
    remainder S depth i h x a a=0 := by
  rw [remainder,updated_self,potential_self,map_zero,add_zero]

@[simp] theorem lowerWord_self (x : XCoord S i) (a : Upper S depth i) :
    lowerWord S depth i h x a a=0 := by
  unfold lowerWord
  rw [remainder_self]
  rfl

theorem coarse_self (a : Upper S depth i) : (coarseSum S depth i h a a).val=0 := word_add_self _

/-- Strict one-X input support holds for every original background. -/
theorem gradient_shift_oneX (x : XCoord S i) (a : Upper S depth i) :
    OneX S depth i h x a (a+gradientError S depth i h x) := by
  change hammingSupport (a+(a+gradientError S depth i h x)) ⊆ _
  rw [← add_assoc,word_add_self,zero_add]
  exact gradientError_supported S depth i h x

theorem gradient_input_x_agreement (x y : XCoord S i) (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y)
        (errorSyndrome S depth i (a+gradientError S depth i h x)).val := by
  have hz : restrictWordLinear ((rxLx S depth i h).syndromeRegion y)
      ((indexedFamily S depth).coboundary1 i.succ (gradientError S depth i h x))=0 := by
    rw [← actual_coboundary1 S depth,
      (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global]
    by_cases hy : y=x
    · subst y
      rw [gradientError_restriction,boundaryGradient_kernel]
    · rw [error_other_x_zero S depth i h x y hy _ (gradientError_supported S depth i h x),map_zero]
  apply eq_of_word_add_zero
  change restrictWordLinear _ ((indexedFamily S depth).coboundary1 i.succ a) +
    restrictWordLinear _ ((indexedFamily S depth).coboundary1 i.succ
      (a+gradientError S depth i h x))=0
  rw [← map_add,← map_add,← add_assoc,word_add_self,zero_add]
  exact hz

/-- The actual canonical Cx outputs agree on the gradient perturbation, even with arbitrary background. -/
theorem gradient_canonical_cx_eq (x y : XCoord S i) (a : Upper S depth i) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h)
        (errorSyndrome S depth i (a+gradientError S depth i h x)).val y :=
  cx_eq_of_read S depth i h _ _ y (gradient_input_x_agreement S depth i h x y a)

private theorem q_component_x_zero (x : XCoord S i) (q : QCoord S i)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (p : LocalRegionIndex ((rxLx S depth i h).correctionRegion x)) :
    cqComponentTotal (rxData S depth i h) sigma q p.val=0 :=
  cqComponentTotal_supported _ _ _ _ (fun hp =>
    (Finset.disjoint_left.mp (x_q_disjoint S depth i h x q)) p.property hp)

/-- The updated X error is the genuine nonzero local gradient; no choice of potential is identified with the witness. -/
theorem gradient_updated_x (x : XCoord S i) (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (updated S depth i h a (a+gradientError S depth i h x)) = boundaryGradient S depth i h x := by
  have hr : restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (run S depth i h a).correction =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x)
        (run S depth i h (a+gradientError S depth i h x)).correction := by
    have hcx : (∑ y : XCoord S i,
        cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y) =
        ∑ y : XCoord S i, cxComponentTotal (rxData S depth i h)
          (errorSyndrome S depth i (a+gradientError S depth i h x)).val y :=
      Finset.sum_congr rfl (fun y _ => gradient_canonical_cx_eq S depth i h x y a)
    have hq : restrictWordLinear ((rxLx S depth i h).correctionRegion x)
        (∑ q : QCoord S i,
          cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val q) =
        restrictWordLinear ((rxLx S depth i h).correctionRegion x)
          (∑ q : QCoord S i, cqComponentTotal (rxData S depth i h)
            (errorSyndrome S depth i (a+gradientError S depth i h x)).val q) := by
      rw [map_sum,map_sum]
      apply Finset.sum_congr rfl
      intro q _
      funext p
      exact (q_component_x_zero S depth i h x q (errorSyndrome S depth i a).val p).trans
        (q_component_x_zero S depth i h x q
          (errorSyndrome S depth i (a+gradientError S depth i h x)).val p).symm
    simpa only [run,rxStepOutput_correction_sum,map_add] using
      congrArg₂ (·+·)
        (congrArg (restrictWordLinear ((rxLx S depth i h).correctionRegion x)) hcx) hq
  have ha : a+(a+gradientError S depth i h x)=gradientError S depth i h x := by
    rw [← add_assoc,word_add_self,zero_add]
  rw [updated,ha,map_add,map_add,hr,add_assoc,word_add_self,add_zero,gradientError_restriction]

theorem gradient_potential_boundary_nonzero (x : XCoord S i) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (potential S depth i h x a (a+gradientError S depth i h x)) ≠ 0 := by
  intro hz
  have he := potential_boundary_x S depth i h x a (a+gradientError S depth i h x)
  rw [hz,map_zero,gradient_updated_x] at he
  exact boundaryGradient_nonzero S depth i h x he.symm

theorem gradient_potential_nonzero (x : XCoord S i) (a : Upper S depth i) :
    potential S depth i h x a (a+gradientError S depth i h x) ≠ 0 := by
  intro hz
  apply gradient_potential_boundary_nonzero S depth i h x a
  rw [hz,map_zero]

/-- The actual nonzero input-syndrome background from the merged Q-block theorem,
combined with the present strict-X perturbation. -/
theorem nonzero_background_consumer (x : XCoord S i) (q : QCoord S i) :
    let a := ((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord (F := BDL26Field) q)
    a ≠ 0 ∧
    (errorSyndrome S depth i a).val
        ((rxData S depth i h).induced.zPairEquiv (BDL26RXQBlockTransport.incidentWitness S i q,0)).val=1 ∧
    OneX S depth i h x a (a+gradientError S depth i h x) ∧
    potential S depth i h x a (a+gradientError S depth i h x) ≠ 0 ∧
    ((indexedDecoderData S depth).selectedMap i).map1
        (lowerWord S depth i h x a (a+gradientError S depth i h x)) =
      updated S depth i h a (a+gradientError S depth i h x) +
        (indexedFamily S depth).coboundary0 i.succ
          (potential S depth i h x a (a+gradientError S depth i h x)) := by
  dsimp only
  exact ⟨BDL26RXQBlockTransport.map1_basis_upper_nonzero S depth i h q,
    BDL26RXQBlockTransport.map1_basis_input_syndrome_witness S depth i h q 0,
    gradient_shift_oneX S depth i h x _,gradient_potential_nonzero S depth i h x _,
    map1_with_potential S depth i h x _ _ (gradient_shift_oneX S depth i h x _)⟩

/-- Complete construction, retaining both actual runs and the original coarse syndrome. -/
theorem two_run (x : XCoord S i) (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (potential S depth i h x a b) ⊆ degreeZeroBlock S depth i h x ∧
      hammingSupport (lowerWord S depth i h x a b) ⊆ incidentQ S depth i x ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x :=
  ⟨map1_with_potential S depth i h x a b he,lower_syndrome S depth i h x a b he,
    potential_supported S depth i h x a b,lower_supported S depth i h x a b he,
    coarse_supported S depth i h x a b he⟩

end QEC.Coding.BDL26RXXStarTransport
