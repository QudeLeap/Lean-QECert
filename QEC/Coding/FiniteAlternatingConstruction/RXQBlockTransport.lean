import QEC.Coding.FiniteAlternatingConstruction.RXErrorPullback

/-!
# Canonical RX transport of one actual Q error block

BDL26 v1 `paper.tex:3459–3461,3465–3481` uses actual correction differences
in its support induction. This project-derived internal lemma constructs the
literal lower word for one Q block of the actual canonical decoder. Its
syndrome occupies incident Z coordinates; no parent-fibre, full-history,
stability, or logical-triviality conclusion is asserted.
-/

noncomputable section
namespace QEC.Coding.BDL26RXQBlockTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem word_add_self {ι : Type*} (w : Word BDL26Field ι) : w+w=0 := by
  funext p
  exact CharTwo.add_self_eq_zero (w p)

private theorem eq_of_word_add_zero {ι : Type*} (u v : Word BDL26Field ι)
    (h : u+v=0) : u=v := by
  have he := congrArg (fun t => u+t) h
  rw [← add_assoc, word_add_self, zero_add, add_zero] at he
  exact he.symm

private theorem zero_off_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word BDL26Field ι) (Y : Finset ι) (hw : hammingSupport w ⊆ Y)
    (p : ι) (hp : p ∉ Y) : w p=0 := by
  by_contra hn
  exact hp (hw (by simpa [hammingSupport] using hn))

private theorem support_of_zero_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word BDL26Field ι) (Y : Finset ι)
    (hw : ∀ p, p ∉ Y → w p=0) : hammingSupport w ⊆ Y := by
  intro p hp
  by_contra hout
  have hn : w p ≠ 0 := by simpa [hammingSupport] using hp
  exact hn (hw p hout)

private theorem restriction_zero_of_disjoint {ι : Type*}
    [Fintype ι] [DecidableEq ι] (w : Word BDL26Field ι) (Y Z : Finset ι)
    (hw : hammingSupport w ⊆ Y) (hd : Disjoint Z Y) :
    restrictWordLinear Z w=0 := by
  funext p
  exact zero_off_support w Y hw p.1 (fun hp =>
    (Finset.disjoint_left.mp hd) p.property hp)

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

private abbrev Data := rxData S depth i h
private abbrev QCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Q
private abbrev XCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.X
private abbrev ZCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Z
private abbrev Syn (S : OddScale) (depth : Nat) (i : StepIndex depth) :=
  (indexedFamily S depth).Cochain2 i.succ

private theorem selected_rx :
    (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl

private theorem actual_coboundary1 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      (indexedFamily S depth).coboundary1 j := rfl

private theorem actual_contract :
    (Data S depth i h).contract = rxContract S depth i h := rfl

/-- The original Tanner orientation has no incoming edge at an X centre. -/
theorem incoming_one_x (x : XCoord S i)
    (v : RXVertex (XCoord S i) (QCoord S i) (ZCoord S i))
    (hv : (Data S depth i h).levelGraph.graph.distance v (.inl x) ≤ 1) :
    v = .inl x := by
  rcases (distance_le_one_iff _ _ _).mp hv with he | he
  · exact he
  · rw [rxData_graph_edge S depth i h, tannerLevel_edge] at he
    rcases v with y | (q | z) <;> simp [vertexEquiv, tannerDirected] at he

/-- Incoming radius one at Q consists of that Q and its incident X vertices. -/
theorem incoming_one_q (q : QCoord S i)
    (v : RXVertex (XCoord S i) (QCoord S i) (ZCoord S i))
    (hv : (Data S depth i h).levelGraph.graph.distance v (.inr (.inl q)) ≤ 1) :
    v = .inr (.inl q) ∨
      ∃ x, v = .inl x ∧ (state S i.val).presentation.xq x q = true := by
  rcases (distance_le_one_iff _ _ _).mp hv with he | he
  · exact Or.inl he
  · rw [rxData_graph_edge S depth i h, tannerLevel_edge] at he
    rcases v with x | (r | z)
    · exact Or.inr ⟨x, rfl, by simpa [vertexEquiv, tannerDirected] using he⟩
    · simp [vertexEquiv, tannerDirected] at he
    · simp [vertexEquiv, tannerDirected] at he

private theorem xi_eq_x (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (x : XCoord S i) :
    rxXiSignal (Data S depth i h) s (.inl x) 1 =
      rxXiSignal (Data S depth i h) t (.inl x) 1 := by
  funext p
  rw [rxXiSignal_apply, rxXiSignal_apply]
  by_cases hd : (Data S depth i h).levelGraph.graph.distance
      ((Data S depth i h).topCenter p) (.inl x) ≤ ((1 : Nat) : WithTop Nat)
  · rw [if_pos hd, if_pos hd]
    have hc := incoming_one_x S depth i h x _
      (by simpa only [Nat.cast_one, WithTop.coe_one] using hd)
    have hp := ((Data S depth i h).topCenter_x_iff x p).mpr hc
    exact congrFun (hx x) ⟨p,hp⟩
  · rw [if_neg hd, if_neg hd]

private theorem xi_eq_q (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (q : QCoord S i)
    (hq : restrictWordLinear ((rxLq S depth i h).syndromeRegion q) s =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) t) :
    rxXiSignal (Data S depth i h) s (.inr (.inl q)) 1 =
      rxXiSignal (Data S depth i h) t (.inr (.inl q)) 1 := by
  funext p
  rw [rxXiSignal_apply, rxXiSignal_apply]
  by_cases hd : (Data S depth i h).levelGraph.graph.distance
      ((Data S depth i h).topCenter p) (.inr (.inl q)) ≤ ((1 : Nat) : WithTop Nat)
  · rw [if_pos hd, if_pos hd]
    rcases incoming_one_q S depth i h q _
      (by simpa only [Nat.cast_one, WithTop.coe_one] using hd) with hc | ⟨x,hc,_⟩
    · exact congrFun hq ⟨p, ((Data S depth i h).topCenter_q_iff q p).mpr hc⟩
    · exact congrFun (hx x) ⟨p, ((Data S depth i h).topCenter_x_iff x p).mpr hc⟩
  · rw [if_neg hd, if_neg hd]

private theorem cx_eq_of_reads (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (x : XCoord S i) :
    cxComponentTotal (Data S depth i h) s x = cxComponentTotal (Data S depth i h) t x := by
  calc
    _ = cxComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) s (.inl x) 1) x :=
      rx_cx_component_invariant _ _ _
    _ = cxComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) t (.inl x) 1) x := by
      rw [xi_eq_x S depth i h s t hx x]
    _ = _ := (rx_cx_component_invariant _ _ _).symm

private theorem cq_eq_of_reads (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (q : QCoord S i)
    (hq : restrictWordLinear ((rxLq S depth i h).syndromeRegion q) s =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) t) :
    cqComponentTotal (Data S depth i h) s q = cqComponentTotal (Data S depth i h) t q := by
  calc
    _ = cqComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) s (.inr (.inl q)) 1) q :=
      rx_q_component_invariant _ _ _
    _ = cqComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) t (.inr (.inl q)) 1) q := by
      rw [xi_eq_q S depth i h s t hx q hq]
    _ = _ := (rx_q_component_invariant _ _ _).symm

/-- Original Q-supported errors have zero actual X restriction. -/
theorem error_x_zero (q : QCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLq S depth i h).correctionRegion q)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).correctionRegion x) e=0 := by
  apply restriction_zero_of_disjoint e _ _ he
  apply Finset.disjoint_left.mpr
  intro p hpx hpq
  apply (Finset.disjoint_left.mp (Data S depth i h).correction_sectors_disjoint)
  · exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hpx⟩
  · rw [(Data S depth i h).qCorrectionSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hpq⟩

theorem error_other_q_zero (q : QCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    restrictWordLinear ((rxLq S depth i h).correctionRegion r) e=0 := by
  exact restriction_zero_of_disjoint e _ _ he
    ((Data S depth i h).cq_correction_regions_pairwise_disjoint r q hr)

/-- X syndrome read equality is derived from the original error difference. -/
theorem input_x_agreement (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i b).val := by
  apply eq_of_word_add_zero
  have hz := (Data S depth i h).contract.support_decomposition.cxDelta1_restriction_global x (a+b)
  rw [error_x_zero S depth i h q (a+b) he x, map_zero] at hz
  rw [actual_coboundary1 S depth] at hz
  simpa only [errorSyndrome, map_add] using hz

/-- Q read equality uses the derived zero-X-error staged restriction. -/
theorem input_other_q_agreement (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion r) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion r) (errorSyndrome S depth i b).val := by
  apply eq_of_word_add_zero
  have hz := (Data S depth i h).contract.support_decomposition.cqDelta1_restriction_global
    r (a+b) (error_x_zero S depth i h q (a+b) he)
  rw [error_other_q_zero S depth i h q (a+b) he r hr, map_zero] at hz
  rw [actual_coboundary1 S depth] at hz
  simpa only [errorSyndrome, map_add] using hz

theorem canonical_cx_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (x : XCoord S i) :
    cxComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val x =
      cxComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val x :=
  cx_eq_of_reads S depth i h _ _ (input_x_agreement S depth i h q a b he) x

theorem canonical_other_cq_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val r =
      cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val r :=
  cq_eq_of_reads S depth i h _ _ (input_x_agreement S depth i h q a b he) r
    (input_other_q_agreement S depth i h q a b he r hr)

/-- Every original X component and every other original Q component cancels. -/
theorem correction_difference_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (run S depth i h a).correction + (run S depth i h b).correction =
      cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val q +
        cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val q := by
  have hx : (∑ x, cxComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val x) =
      ∑ x, cxComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val x := by
    apply Finset.sum_congr rfl
    intro x _
    exact canonical_cx_eq S depth i h q a b he x
  rw [run, run, rxStepOutput_correction_sum, rxStepOutput_correction_sum, hx]
  calc
    _ = (∑ x, cxComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val x) +
        (∑ x, cxComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val x) +
        ((∑ r, cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val r) +
          ∑ r, cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val r) := by abel
    _ = ∑ r, (cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val r +
        cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val r) := by
      rw [word_add_self, zero_add, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_eq_single q
      · intro r _ hr
        rw [canonical_other_cq_eq S depth i h q a b he r hr, word_add_self]
      · simp

private theorem cq_component_supported (sigma : Syn S depth i) (q : QCoord S i) :
    hammingSupport (cqComponentTotal (Data S depth i h) sigma q) ⊆
      (rxLq S depth i h).correctionRegion q :=
  support_of_zero_off (cqComponentTotal (Data S depth i h) sigma q)
    ((rxLq S depth i h).correctionRegion q)
    (fun p hp => cqComponentTotal_supported (Data S depth i h) sigma q p hp)

theorem correction_difference_supported (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport ((run S depth i h a).correction + (run S depth i h b).correction) ⊆
      (rxLq S depth i h).correctionRegion q := by
  rw [correction_difference_eq S depth i h q a b he]
  exact Finset.Subset.trans (hammingSupport_add_subset_union _ _)
    (Finset.union_subset (cq_component_supported S depth i h _ q)
      (cq_component_supported S depth i h _ q))

theorem updated_supported (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport (updated S depth i h a b) ⊆ (rxLq S depth i h).correctionRegion q := by
  apply support_of_zero_off
  intro p hp
  have h1 := zero_off_support (a+b) _ he p hp
  have h2 := zero_off_support _ _ (correction_difference_supported S depth i h q a b he) p hp
  change (a p+b p)+(run S depth i h a).correction p+(run S depth i h b).correction p=0
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0 at h2
  change a p+b p=0 at h1
  rw [h1, zero_add]
  exact h2

private theorem map2_x_zero (s : (indexedFamily S depth).Cochain2 i.castSucc)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).selectedMap i).map2 s)=0 := by
  rw [selected_rx]
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.1) _ hz
  rw [(Data S depth i h).xSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.property⟩

private theorem map2_q_zero (s : (indexedFamily S depth).Cochain2 i.castSucc)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (((indexedDecoderData S depth).selectedMap i).map2 s)=0 := by
  rw [selected_rx]
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.2) _ hz
  rw [(Data S depth i h).qSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, p.property⟩

theorem updated_q_kernel (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
        (updated S depth i h a b))=0 := by
  have hk := (Data S depth i h).contract.support_decomposition.cqDelta1_restriction_global q
    (updated S depth i h a b)
    (error_x_zero S depth i h q _ (updated_supported S depth i h q a b he))
  rw [actual_contract S depth i h, actual_coboundary1 S depth] at hk
  rw [updated_delta, map2_q_zero] at hk
  exact hk.symm

/-- The coefficient is read from the complete actual updated word, not chosen. -/
def rootCoefficient (q : QCoord S i) (a b : Upper S depth i) : BDL26Field :=
  updated S depth i h a b
    (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val

def lowerWord (q : QCoord S i) (a b : Upper S depth i) : Lower S depth i :=
  rootCoefficient S depth i h q a b • canonicalBasisWord q

/-- The constructed full upper potential is literally zero. -/
def potential (_even : i.val % 2=0) : Potential S depth i := 0

@[simp] theorem potential_eq_zero : potential S depth i h=0 := rfl

@[simp] theorem potential_delta_zero :
    (indexedFamily S depth).coboundary0 i.succ (potential S depth i h)=0 := map_zero _

@[simp] theorem potential_delta_delta_zero :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h))=0 := by
  rw [potential_delta_zero, map_zero]

/-- Complete map1 identity, including every auxiliary upper coordinate. -/
theorem map1_basis_eq_updated (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b) =
      updated S depth i h a b := by
  rw [selected_rx, rxMap1_constant_Q S depth i h]
  have hs : (∑ r, extendWordLinear ((rxLq S depth i h).correctionRegion r)
      (fun _ => lowerWord S depth i h q a b r)) =
      extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (fun _ => rootCoefficient S depth i h q a b) := by
    rw [Finset.sum_eq_single q]
    · simp [lowerWord, canonicalBasisWord]
    · intro r _ hr
      have hz : lowerWord S depth i h q a b r=0 := by
        simp [lowerWord, canonicalBasisWord, hr]
      simp only [hz]
      exact map_zero _
    · simp
  rw [hs]
  funext p
  by_cases hp : p ∈ (rxLq S depth i h).correctionRegion q
  · change extendLocalSignal ((rxLq S depth i h).correctionRegion q)
      (fun _ => rootCoefficient S depth i h q a b) p = updated S depth i h a b p
    rw [extendLocalSignal, dif_pos hp]
    let u : LocalRegionIndex ((rxLq S depth i h).correctionRegion q) := ⟨p,hp⟩
    obtain ⟨v,hv⟩ := (rxQVertexEquiv S depth i h q).surjective u
    have hc := rxQ_kernel_constant S depth i h q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
        (updated S depth i h a b)) (updated_q_kernel S depth i h q a b he) v
    rw [hv] at hc
    change updated S depth i h a b p = rootCoefficient S depth i h q a b at hc
    exact hc.symm
  · rw [show extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (fun _ => rootCoefficient S depth i h q a b) p=0 by
          exact dif_neg hp]
    exact (zero_off_support _ _ (updated_supported S depth i h q a b he) p hp).symm

theorem map1_with_potential (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b) =
      updated S depth i h a b +
        (indexedFamily S depth).coboundary0 i.succ (potential S depth i h) := by
  rw [potential_delta_zero, add_zero, map1_basis_eq_updated S depth i h q a b he]

private theorem map2_injective (h : i.val % 2=0) :
    Function.Injective ((indexedDecoderData S depth).selectedMap i).map2 := by
  intro u v huv
  rw [selected_rx] at huv
  funext z
  have he := congrFun huv ((Data S depth i h).induced.zPairEquiv (z,0)).val
  simpa only [(Data S depth i h).induced.map2_diagonal] using he

theorem lower_syndrome (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h q a b) =
      (coarseSum S depth i h a b).val := by
  apply map2_injective S depth i h
  have hc := LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (lowerWord S depth i h q a b)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h q a b)) at hc
  rw [map1_basis_eq_updated S depth i h q a b he, updated_delta] at hc
  exact hc.symm

theorem lower_supported (q : QCoord S i) (a b : Upper S depth i) :
    hammingSupport (lowerWord S depth i h q a b) ⊆ {q} := by
  apply support_of_zero_off
  intro r hr
  have hne : r≠q := by simpa only [Finset.mem_singleton] using hr
  simp [lowerWord, canonicalBasisWord, hne]

theorem coarse_difference_apply (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      if (state S i.val).presentation.qz q z=true then rootCoefficient S depth i h q a b else 0 := by
  rw [← lower_syndrome S depth i h q a b he, lowerWord, map_smul,
    indexedFamily_coboundary1]
  change rootCoefficient S depth i h q a b *
      tannerCoboundary1 (state S i.val).presentation (canonicalBasisWord q) z = _
  rw [tannerCoboundary1_canonicalBasis_apply]
  by_cases hz : (state S i.val).presentation.qz q z=true <;> simp [hz]

/-- The actual incident-Z carrier, distinct from a Q-labelled owner fibre. -/
def incidentZ (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => (state S i.val).presentation.qz q z=true

theorem coarse_support_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport (coarseSum S depth i h a b).val =
      if rootCoefficient S depth i h q a b=0 then ∅ else incidentZ S i q := by
  ext z
  by_cases ha : rootCoefficient S depth i h q a b=0
  · simp [hammingSupport, coarse_difference_apply S depth i h q a b he, ha]
  · by_cases hz : (state S i.val).presentation.qz q z=true <;>
      simp [hammingSupport, coarse_difference_apply S depth i h q a b he, ha, incidentZ, hz]

theorem selected_image_pair (q : QCoord S i) (a b : Upper S depth i)
    (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((Data S depth i h).induced.zPairEquiv (z,copy)).val =
        (coarseSum S depth i h a b).val z := by
  rw [selected_rx]
  exact (Data S depth i h).induced.map2_diagonal _ _ _

theorem selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (Data S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 := by
  rw [selected_rx]
  exact (Data S depth i h).induced.map2_auxiliary_zero _ p
    (by simpa only [← (Data S depth i h).zSector_eq_induced] using hp)

/-- Both genuine old-Z copies of the actual incident-Z carrier. -/
def twoCopyIncidentZ (q : QCoord S i) : Finset (FamilyZ S depth i.succ) :=
  ((incidentZ S i q).product (Finset.univ : Finset (Fin 2))).image
    (fun zc => ((Data S depth i h).induced.zPairEquiv zc).val)

private theorem twoCopy_eq_biUnion (q : QCoord S i) :
    twoCopyIncidentZ S depth i h q =
      (incidentZ S i q).biUnion (zPairImage (Data S depth i h)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨z,c⟩,hzc,hp⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨z,(Finset.mem_product.mp hzc).1,
      Finset.mem_image.mpr ⟨c,Finset.mem_univ _,hp⟩⟩
  · intro hp
    obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨(z,c),Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩,hc⟩

theorem selected_image_support_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) =
      if rootCoefficient S depth i h q a b=0 then ∅ else twoCopyIncidentZ S depth i h q := by
  rw [selected_rx, map2_support_eq_biUnion (Data S depth i h),
    coarse_support_eq S depth i h q a b he]
  by_cases ha : rootCoefficient S depth i h q a b=0
  · simp [ha]
  · rw [if_neg ha, if_neg ha, twoCopy_eq_biUnion]

/-- A named complete construction, retaining its full zero potential. -/
theorem two_run (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (potential S depth i h) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h q a b) =
        (coarseSum S depth i h a b).val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val =
        (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h))=0 :=
  ⟨map1_with_potential S depth i h q a b he, lower_syndrome S depth i h q a b he,
    (updated_delta S depth i h a b).symm, potential_delta_delta_zero S depth i h⟩

theorem updated_self (a : Upper S depth i) : updated S depth i h a a=0 := by
  unfold updated
  rw [word_add_self, zero_add, word_add_self]

@[simp] theorem rootCoefficient_self (q : QCoord S i) (a : Upper S depth i) :
    rootCoefficient S depth i h q a a=0 := by
  rw [rootCoefficient, updated_self]
  rfl

@[simp] theorem lowerWord_self (q : QCoord S i) (a : Upper S depth i) :
    lowerWord S depth i h q a a=0 := by
  rw [lowerWord, rootCoefficient_self, zero_smul]

theorem coarse_self (a : Upper S depth i) : (coarseSum S depth i h a a).val=0 :=
  word_add_self _

private theorem shift_syndrome_difference (a : Upper S depth i) (w : Lower S depth i) :
    (errorSyndrome S depth i a).val +
      (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val =
      ((indexedDecoderData S depth).selectedMap i).map2
        ((indexedFamily S depth).coboundary1 i.castSucc w) := by
  change (indexedFamily S depth).coboundary1 i.succ a +
      (indexedFamily S depth).coboundary1 i.succ
        (a+((indexedDecoderData S depth).selectedMap i).map1 w) = _
  rw [map_add, ← add_assoc, word_add_self, zero_add]
  exact LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1) w

private theorem shift_x_agreement (a : Upper S depth i) (w : Lower S depth i)
    (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
        (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val := by
  apply eq_of_word_add_zero
  rw [← map_add, shift_syndrome_difference, map2_x_zero]

private theorem shift_q_agreement (a : Upper S depth i) (w : Lower S depth i)
    (q : QCoord S i) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val := by
  apply eq_of_word_add_zero
  rw [← map_add, shift_syndrome_difference, map2_q_zero]

/-- Original canonical corrections agree on every background under an actual map1 shift. -/
theorem correction_add_map1_eq (a : Upper S depth i) (w : Lower S depth i) :
    (run S depth i h (a+((indexedDecoderData S depth).selectedMap i).map1 w)).correction =
      (run S depth i h a).correction := by
  have hx := shift_x_agreement S depth i h a w
  have hq := shift_q_agreement S depth i h a w
  rw [run, run, rxStepOutput_correction_sum, rxStepOutput_correction_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    exact (cx_eq_of_reads S depth i h _ _ hx x).symm
  · apply Finset.sum_congr rfl
    intro q _
    exact (cq_eq_of_reads S depth i h _ _ hx q (hq q)).symm

theorem updated_add_map1 (a : Upper S depth i) (w : Lower S depth i) :
    updated S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w) =
      ((indexedDecoderData S depth).selectedMap i).map1 w := by
  rw [updated, correction_add_map1_eq]
  calc
    _ = (a+a) + ((indexedDecoderData S depth).selectedMap i).map1 w +
        ((run S depth i h a).correction+(run S depth i h a).correction) := by abel
    _ = _ := by rw [word_add_self, word_add_self, zero_add, add_zero]

theorem coarse_add_map1 (a : Upper S depth i) (w : Lower S depth i) :
    (coarseSum S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val =
      (indexedFamily S depth).coboundary1 i.castSucc w := by
  apply map2_injective S depth i h
  rw [← updated_delta, updated_add_map1]
  exact LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1) w

/-- The actual lift of a basis is supported in its own actual Q block. -/
theorem map1_basis_supported (q : QCoord S i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord q)) ⊆ (rxLq S depth i h).correctionRegion q := by
  rw [selected_rx, rxMap1_constant_Q S depth i h]
  apply support_of_zero_off
  intro p hp
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r=q
  · subst r
    exact dif_neg hp
  · have hz : canonicalBasisWord (F := BDL26Field) q r=0 := by
      simp [canonicalBasisWord, hr]
    simp only [hz]
    exact congrFun (map_zero (extendWordLinear ((rxLq S depth i h).correctionRegion r))) p

theorem map1_basis_error_support (q : QCoord S i) (a : Upper S depth i) :
    hammingSupport (a+(a+((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord q))) ⊆ (rxLq S depth i h).correctionRegion q := by
  rw [← add_assoc, word_add_self, zero_add]
  exact map1_basis_supported S depth i h q

private theorem map1_at_cone (w : Lower S depth i) (q : QCoord S i) :
    ((indexedDecoderData S depth).selectedMap i).map1 w
      (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val = w q := by
  rw [selected_rx, rxMap1_constant_Q S depth i h, Finset.sum_apply, Finset.sum_eq_single q]
  · change extendLocalSignal ((rxLq S depth i h).correctionRegion q) (fun _ => w q)
        (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val = w q
    simp only [extendLocalSignal, dif_pos (rxQVertexEquiv S depth i h q
      (0, Sum.inl (Sum.inl ()))).property]
  · intro r _ hr
    have hp : (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val ∉
        (rxLq S depth i h).correctionRegion r := by
      intro hp
      exact (Finset.disjoint_left.mp
        ((Data S depth i h).cq_correction_regions_pairwise_disjoint r q hr)) hp
          (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).property
    exact dif_neg hp
  · simp

theorem map1_basis_consumer (q : QCoord S i) (a : Upper S depth i) :
    rootCoefficient S depth i h q a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))=1 ∧
      lowerWord S depth i h q a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))=
          canonicalBasisWord q ∧
      (coarseSum S depth i h a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val =
          (indexedFamily S depth).coboundary1 i.castSucc (canonicalBasisWord q) := by
  have hc : rootCoefficient S depth i h q a
      (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))=1 := by
    rw [rootCoefficient, updated_add_map1, map1_at_cone]
    simp [canonicalBasisWord]
  refine ⟨hc, ?_, coarse_add_map1 S depth i h a (canonicalBasisWord q)⟩
  rw [lowerWord, hc, one_smul]

/-- The actual construction supplies a nonzero syndrome coordinate for every lower basis. -/
def incidentWitness (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) : ZCoord S i :=
  ((state S i.val).admissible.toTannerSquareAdmissible.qzRoot q).val

theorem incidentWitness_mem (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) :
    (state S i.val).presentation.qz q (incidentWitness S i q)=true :=
  ((state S i.val).admissible.toTannerSquareAdmissible.qzRoot q).property

theorem map1_basis_coarse_witness (q : QCoord S i) (a : Upper S depth i) :
    (coarseSum S depth i h a
      (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
        (incidentWitness S i q)=1 := by
  rw [coarse_add_map1, indexedFamily_coboundary1,
    tannerCoboundary1_canonicalBasis_apply]
  simpa only [Fin.val_castSucc, if_pos (incidentWitness_mem S i q)]

theorem map1_basis_lower_nonzero (q : QCoord S i) (a : Upper S depth i) :
    lowerWord S depth i h q a
      (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q)) ≠ 0 := by
  rw [(map1_basis_consumer S depth i h q a).2.1]
  intro he
  have ht := congrFun he q
  simpa [canonicalBasisWord] using ht

theorem map1_basis_upper_nonzero (h : i.val % 2=0) (q : QCoord S i) :
    ((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord (F := BDL26Field) q) ≠ 0 := by
  intro he
  have ht := congrFun he (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val
  rw [map1_at_cone] at ht
  simpa [canonicalBasisWord] using ht

theorem map1_basis_pair_witness (q : QCoord S i) (a : Upper S depth i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
      ((Data S depth i h).induced.zPairEquiv (incidentWitness S i q,copy)).val=1 := by
  rw [selected_image_pair S depth i h q,
    map1_basis_coarse_witness S depth i h q a]

/-- The nonzero lifted background also has a genuine nonzero input syndrome. -/
theorem map1_basis_input_syndrome_witness (q : QCoord S i) (copy : Fin 2) :
    (errorSyndrome S depth i
      (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
      ((Data S depth i h).induced.zPairEquiv (incidentWitness S i q,copy)).val=1 := by
  have hc := LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (canonicalBasisWord (F := BDL26Field) q)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (canonicalBasisWord q)) at hc
  change (indexedFamily S depth).coboundary1 i.succ
    (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q)) _=1
  rw [hc, selected_rx, (Data S depth i h).induced.map2_diagonal,
    indexedFamily_coboundary1, tannerCoboundary1_canonicalBasis_apply]
  simpa only [Fin.val_castSucc, if_pos (incidentWitness_mem S i q)]

end QEC.Coding.BDL26RXQBlockTransport
