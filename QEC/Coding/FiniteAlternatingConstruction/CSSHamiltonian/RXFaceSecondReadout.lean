import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXFaceEdgeTower

/-!
# Actual SECOND readouts in the RX face-edge tower

Internal calculations on the literal original RX selectors. The
finite crossing and local budget arguments below keep the actual syndrome
translation and do not choose a normalization for an original Cq witness.
-/
noncomputable section
namespace QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators

private theorem bit_cases (c : F) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem word_add_self {I : Type} (w : Word F I) : w+w=0 := by
  funext i
  exact ZModModule.add_self (w i)

private theorem support_ne {I : Type} [Fintype I]
    (w : Word F I) (i : I) (hi : i∈hammingSupport w) : w i≠0 :=
  (Finset.mem_filter.mp hi).2

private theorem support_subset_of_nonzero {I : Type} [Fintype I]
    (w : Word F I) (s : Finset I) (h : ∀ i, w i≠0 → i∈s) :
    hammingSupport w⊆s := by
  intro i hi
  exact h i (support_ne w i hi)

private theorem eval_sum {I J : Type} [Fintype I]
    (f : I → Word F J) (p : J) : (∑ i,f i) p=∑ i,f i p := by
  simp only [Finset.sum_apply]

private theorem incidence_square_sum (T : TannerSquarePresentation)
    (x : T.X) (z : T.Z) :
    (∑ q : T.Q,(if T.xq x q=true then (1:F) else 0)*
      (if T.qz q z=true then 1 else 0))=0 := by
  have hz := congrFun (LinearMap.congr_fun (tannerCoboundary_squared T)
    (canonicalBasisWord (F:=F) x)) z
  change (∑ q : T.Q,tannerCoboundary0 T (canonicalBasisWord (F:=F) x) q*
    (if T.qz q z=true then 1 else 0))=0 at hz
  simpa only [tannerCoboundary0_canonicalBasis_apply] using hz

private theorem sum_shifted_product_of_zero {I : Type} [Fintype I]
    (u x y : I → F) (b : F) (h : (∑ i,x i*y i)=0) :
    (∑ i,(u i*y i+b*x i*y i))=∑ i,u i*y i := by
  have he : (∑ i,(u i*y i+b*x i*y i))=
      (∑ i,u i*y i)+b*(∑ i,x i*y i) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
  exact he.trans (by rw [h,mul_zero,add_zero])

private theorem shifted_tanner_syndrome (T : TannerSquarePresentation)
    (x : T.X) (u : Word F T.Q) (b : F) (z : T.Z) :
    (∑ q : T.Q,(u q*(if T.qz q z=true then 1 else 0)+
      b*(if T.xq x q=true then 1 else 0)*
        (if T.qz q z=true then 1 else 0)))=tannerCoboundary1 T u z := by
  exact (sum_shifted_product_of_zero u
    (fun q => if T.xq x q=true then 1 else 0)
    (fun q => if T.qz q z=true then 1 else 0) b
    (incidence_square_sum T x z)).trans rfl

private theorem word_equiv_forward_apply {I J : Type} (e : I ≃ J)
    (w : Word F I) (i : I) : wordEquiv e w (e i)=w i := by
  simp only [wordEquiv_apply,Equiv.symm_apply_apply]

private theorem old_z_not_q_region (T : TannerSquarePresentation) (S : OddScale)
    (q : T.Q) (z : T.Z) (c : BDL26FiniteTannerSquare.Two) :
    Sum.inr (z,c)∉(localQ T S).syndromeRegion q := by
  intro hz
  have he := (Finset.mem_filter.mp hz).2
  change (Vertex.z z : Vertex T)=Vertex.q q at he
  cases he

private theorem physical_star_mem (T : TannerSquarePresentation) (x : T.X) (q : T.Q) :
    q∈BDL26RXPhysicalStarTransport.physicalXStar T x ↔ T.xq x q=true := by
  simp only [BDL26RXPhysicalStarTransport.physicalXStar,Finset.mem_filter,
    Finset.mem_univ,true_and]

private theorem incident_word_supported (T : TannerSquarePresentation) (x : T.X)
    (w : Word F T.Q) :
    hammingSupport (fun q => if T.xq x q=true then w q else 0)⊆
      BDL26RXPhysicalStarTransport.physicalXStar T x := by
  intro q hq
  by_cases hi : T.xq x q=true
  · exact (physical_star_mem T x q).mpr hi
  · exact False.elim (support_ne _ q hq (if_neg hi))

private theorem xq_commutes_apply (T : TannerSquarePresentation)
    (A : TannerSquareAdmissible T) (q : T.Q) (x : T.X)
    (hxq : T.xq x q=true) (S : OddScale)
    (g : Word F (DoubleCylinderVertex T x S)) (edge : QDoubleCylinderEdge T q S) :
    rxXQDegreeOne T A q x hxq S
      (wordLinearMapTranspose (doubleCylinderBoundary1 T x S) g) edge=
    wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S)
      (rxXQDegreeZero T A q x hxq S g) edge := by
  have hc := LinearMap.congr_fun (rxXQ_commutes T A q x hxq S) g
  rw [LinearMap.comp_apply,LinearMap.comp_apply] at hc
  exact (congrFun hc edge).symm

private theorem x_flow_gradient_at_q (T : TannerSquarePresentation)
    (A : TannerSquareAdmissible T) (S : OddScale) (x : T.X)
    (g : Word F (DoubleCylinderVertex T x S)) (q : T.Q)
    (edge : QDoubleCylinderEdge T q S) (hxq : T.xq x q=true) :
    xFlow T S x (wordLinearMapTranspose (doubleCylinderBoundary1 T x S) g)
      (Sum.inl (Sum.inr ⟨q,edge⟩))=
    wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S)
      (rxXQDegreeZero T A q x hxq S g) edge := by
  rw [xFlow_at_q T A,dif_pos hxq]
  exact xq_commutes_apply T A q x hxq S g edge

private theorem local_q_transport (T : TannerSquarePresentation) (S : OddScale)
    (q : T.Q) (g : Word F (QDoubleCylinderVertex T q S)) :
    wordLinearMapTranspose (localCq T S q).boundary2
      (wordEquiv (qCorrectionEquiv T S q) g)=
      wordEquiv (qSyndromeEquiv T S q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S) g) := by
  funext j
  obtain ⟨edge,rfl⟩ := (qSyndromeEquiv T S q).surjective j
  rw [localCq_delta1_apply,LinearEquiv.symm_apply_apply]
  simp only [wordEquiv_apply,Equiv.symm_apply_apply]

private theorem raw_q_delta (T : TannerSquarePresentation) (S : OddScale)
    (q : T.Q) (u : Word F (LocalRegionIndex ((localQ T S).correctionRegion q)))
    (g : Word F (QDoubleCylinderVertex T q S))
    (hlocal : wordLinearMapTranspose (localCq T S q).boundary2 u=
      wordEquiv (qSyndromeEquiv T S q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S) g)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S)
      ((wordEquiv (qCorrectionEquiv T S q)).symm u)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 T q S) g := by
  funext edge
  exact ((localCq_delta1_apply T S q u edge).symm.trans
    (congrFun hlocal (qSyndromeEquiv T S q edge))).trans
    (word_equiv_forward_apply (qSyndromeEquiv T S q) _ edge)

/-- A genuine original syndrome, constructed from its full physical word. -/
def physicalInput (S : OddScale) (n : Nat) (e : Word F (Physical S (n+2))) :
    XSyndromeDomain S n := ⟨zSyndrome S (n+2) e,⟨e,rfl⟩⟩

@[simp] theorem physicalInput_translate (S : OddScale) (n : Nat)
    (a b : Word F (Physical S (n+2))) :
    translateX S n (physicalInput S n a) b=physicalInput S n (a+b) := by
  apply Subtype.ext
  exact (map_add (zSyndrome S (n+2)) a b).symm

/-- Read the original fixed-total history of the actual physical word. -/
def physicalReadout (S : OddScale) (n : Nat) (e : Word F (Physical S (n+2))) :=
  firstReadout S n (physicalInput S n e)

theorem physical_second (S : OddScale) (n : Nat)
    (a : Word F (Physical S (n+2))) (q : Physical S (n+2)) :
    secondReadout S n (physicalInput S n a) q=
      physicalReadout S n (a+BDL26ActualFailureReadout.flip S n q) := by
  unfold secondReadout physicalReadout
  rw [input_translate,physicalInput_translate]
  rfl

/-- A finite walk that leaves the zero readout has an actual adjacent crossing.
The supplied finite set lists physical flips; no decoder output is normalized. -/
private theorem finite_crossing {I J : Type} [DecidableEq I] [Zero J]
    (readout : Word F I → J) (s : Finset I) (a : Word F I)
    (ha : readout a=0)
    (hb : readout (a+∑ q∈s,Pi.single q (1:F))≠0) :
    ∃ b q, q∈s ∧ readout b=0 ∧ readout (b+Pi.single q (1:F))≠0 := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
      exfalso
      exact hb (by simpa only [Finset.sum_empty,add_zero] using ha)
  | @insert q s hq ih =>
      rw [Finset.sum_insert hq] at hb
      by_cases hnext : readout (a+Pi.single q (1:F))=0
      · have htail : readout ((a+Pi.single q (1:F))+∑ r∈s,Pi.single r (1:F))≠0 := by
          simpa only [add_assoc] using hb
        obtain ⟨b,r,hr,hb0,hb1⟩ := ih _ hnext htail
        exact ⟨b,r,Finset.mem_insert_of_mem hr,hb0,hb1⟩
      · exact ⟨a,q,Finset.mem_insert_self _ _,ha,hnext⟩

private theorem word_eq_support_flips {I : Type} [Fintype I] [DecidableEq I]
    (e : Word F I) : (∑ q∈hammingSupport e,Pi.single q (1:F))=e := by
  funext r
  by_cases hr : e r=0
  · have hm : r∉hammingSupport e := by simp [hammingSupport,hr]
    simp [Finset.sum_apply,Pi.single_apply,hm,hr]
  · have hm : r∈hammingSupport e := by simp [hammingSupport,hr]
    have hone : e r=1 := (bit_cases (e r)).resolve_left hr
    simp [Finset.sum_apply,Pi.single_apply,hm,hone]

/-- Physical crossing, retaining exactly the original input, perturbation and
FIRST/SECOND operations. The nonzero endpoint will be constructed below. -/
theorem physical_crossing (S : OddScale) (n : Nat)
    (e : Word F (Physical S (n+2)))
    (hzero : physicalReadout S n 0=0) (hne : physicalReadout S n e≠0) :
    ∃ (a : Word F (Physical S (n+2))) (q : Physical S (n+2)),
      q∈hammingSupport e ∧ firstReadout S n (physicalInput S n a)=0 ∧
      secondReadout S n (physicalInput S n a) q≠0 := by
  have he : physicalReadout S n (0+∑ q∈hammingSupport e,Pi.single q (1:F))≠0 := by
    simpa only [zero_add,word_eq_support_flips] using hne
  obtain ⟨a,q,hq,ha,hb⟩ := finite_crossing (physicalReadout S n)
    (hammingSupport e) 0 hzero he
  exact ⟨a,q,hq,ha,by simpa only [physical_second,BDL26ActualFailureReadout.flip] using hb⟩

/-- Original Cq preimages differ by one constant on the actual connected graph.
This applies to every preimage, independently of which admissible witness the
unchanged Classical.choose selector returns. -/
theorem q_preimage_difference (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (g h : Word F (QDoubleCylinderVertex P q S))
    (he : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) g=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) h) :
    ∀ v, h v+g v=h (0,Sum.inl (Sum.inl ()))+g (0,Sum.inl (Sum.inl ())) := by
  have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (h+g)=0 := by
    rw [map_add,he,word_add_self]
  exact word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0,Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S) (h+g)
    (by simpa only [qDoubleCylinderBoundary1] using hz)

/-- The legitimate smallest scale is used only to avoid subdivision interiors. -/
def witnessScale : OddScale := ⟨3,by decide,by decide⟩

@[simp] theorem witnessScale_half : witnessScale.half=1 := rfl

private theorem witness_half_card [inst : Fintype (Fin witnessScale.half)] :
    (Finset.univ : Finset (Fin witnessScale.half)).card=1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨⟨0, by change 0<1; decide⟩,?_⟩
  ext i
  constructor
  · intro _
    apply Finset.mem_singleton.mpr
    apply Fin.ext
    change i.val=0
    have hi := i.isLt
    change i.val<1 at hi
    omega
  · intro _
    exact Finset.mem_univ i

private theorem witness_half_fintype_card [inst : Fintype (Fin witnessScale.half)] :
    Fintype.card (Fin witnessScale.half)=1 := by
  simpa only [Finset.card_univ] using (witness_half_card (inst:=inst))

private theorem witness_index_zero (i : Fin witnessScale.half) : i.val=0 := by
  have hi := i.isLt
  change i.val<1 at hi
  omega

private theorem witness_index_last (i : Fin witnessScale.half) :
    i.val+1=witnessScale.half := by
  change i.val+1=1
  rw [witness_index_zero]

private theorem witness_subdivision_start (P : TannerSquarePresentation) (q : P.Q)
    (edge : QSubdivisionEdge P q witnessScale) :
    qSubdivisionEdgeStart P q witnessScale edge=
      Sum.inl (qStarEdgeStart P q edge.1) := by
  unfold qSubdivisionEdgeStart
  rw [dif_pos (witness_index_zero edge.2)]

private theorem witness_subdivision_end (P : TannerSquarePresentation) (q : P.Q)
    (edge : QSubdivisionEdge P q witnessScale) :
    qSubdivisionEdgeEnd P q witnessScale edge=
      Sum.inl (qStarEdgeEnd P q edge.1) := by
  unfold qSubdivisionEdgeEnd
  rw [dif_pos (witness_index_last edge.2)]

/-- Copy-separated cone roots and the same prescribed bit at every Z port. -/
def qPortWord (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    Word F (QDoubleCylinderVertex P q witnessScale) := fun v =>
  match v.2 with
  | Sum.inl (Sum.inl _) => if v.1=0 then 0 else 1
  | _ => b

@[simp] theorem qPortWord_root (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    qPortWord P q b (0,Sum.inl (Sum.inl ()))=0 := rfl

@[simp] theorem qPortWord_leaf (P : TannerSquarePresentation) (q : P.Q) (b : F)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    qPortWord P q b (c,Sum.inl (Sum.inr z))=b := rfl

/-- Each actual cone-to-port pair contributes precisely one input edge. -/
theorem qPortWord_syndrome_weight (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
      (qPortWord P q b))=Fintype.card (QStarEdge P q) := by
  have hweight : HammingWeight
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) (qPortWord P q b))=
      ∑ edge : QDoubleCylinderEdge P q witnessScale,
        if wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
          (qPortWord P q b) edge=0 then 0 else 1 := by
    simp [HammingWeight,hammingSupport,Finset.card_filter]
  rw [hweight]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp_rw [qLocalCoboundary_apply]
  rcases bit_cases b with rfl | rfl <;>
    simp [-witnessScale_half,-Fintype.card_fin,Fin.sum_univ_two,
      witness_subdivision_start,witness_subdivision_end,witness_half_card,
      witness_half_fintype_card,Finset.card_univ,ZModModule.add_self,
      qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,
      qStarEdgeStart,qStarEdgeEnd,
      qPortWord]


/-- The actual outgoing flow counts both copies of every incident Z port. -/
theorem full_port_weight (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (h : Word F (QDoubleCylinderVertex P q S))
    (hleaf : ∀ (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two),
      h (c,Sum.inl (Sum.inr z))=1) :
    HammingWeight (BDL26RXDecoderAdapter.qFlow P S q h)=
      2*Fintype.card (QStarEdge P q) := by
  rw [BDL26RXDecoderAdapter.qFlow_weight,
    BDL26ReplacementSupport.rxQOutgoing_sum_weight]
  have hport : ∀ z : QStarEdge P q,
      rxQZDegreeOne P q z.1 z.2 S h=(fun _ : BDL26FiniteTannerSquare.Two => (1:F)) := by
    intro z
    funext c
    exact hleaf z c
  simp only [hport]
  simp [HammingWeight,hammingSupport,Nat.mul_comm]

/-- A budget forces the cone-root branch when both actual Z endpoints carry
one common bit. It quantifies over EVERY admissible original local preimage;
Classical.choose is not replaced, and mixed-endpoint ties are not resolved. -/
theorem q_branch_forced (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (b : F) (h : Word F (QDoubleCylinderVertex P q witnessScale))
    (hdelta : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) h=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
        (qPortWord P q b))
    (hbudget : HammingWeight (BDL26RXDecoderAdapter.qFlow P witnessScale q h) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
        (qPortWord P q b))) :
    h (0,Sum.inl (Sum.inl ()))=b := by
  by_contra hbad
  have hleaf : ∀ (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two),
      h (c,Sum.inl (Sum.inr z))=1 := by
    intro z c
    have hv := q_preimage_difference P A witnessScale q (qPortWord P q b) h
      hdelta.symm (c,Sum.inl (Sum.inr z))
    rw [qPortWord_leaf,qPortWord_root,add_zero] at hv
    have hn : h (c,Sum.inl (Sum.inr z))≠0 := by
      intro hz
      rw [hz,zero_add] at hv
      exact hbad hv.symm
    exact (bit_cases _).resolve_left hn
  rw [full_port_weight P witnessScale q h hleaf,
    qPortWord_syndrome_weight] at hbudget
  have hp : 0<Fintype.card (QStarEdge P q) :=
    Fintype.card_pos_iff.mpr ⟨A.qzRoot q⟩
  omega


private abbrev rxIndex : StepIndex 3 := ⟨2,by decide⟩
private theorem rxIndex_even : rxIndex.val%2=0 := by decide

/-- At n=1 the original fixed-total history makes exactly the actual C3 RX
step. This equality uses the original history input and its genuine range proof. -/
theorem physicalReadout_one (S : OddScale) (e : Word F (Physical S 3)) :
    physicalReadout S 1 e=
      (BDL26RXErrorPullback.run S 3 rxIndex rxIndex_even e).coarse.val := by
  have hs := congrArg Subtype.val (actualInputs_step S 1
    (input S 1 (physicalInput S 1 e)) (⟨0,by decide⟩ : StepIndex 1))
  change physicalReadout S 1 e=
    (actualStep S 3 rxIndex
      (actualInputs S 1 (input S 1 (physicalInput S 1 e)) (TopIndex 1))).coarse.val at hs
  rw [actualInputs_top,actualStep_rx S 3 rxIndex rxIndex_even] at hs
  have hin : input S 1 (physicalInput S 1 e)=
      BDL26RXErrorPullback.errorSyndrome S 3 rxIndex e := by
    apply Subtype.ext
    change zSyndrome S 3 e=(indexedFamily S 3).coboundary1 rxIndex.succ e
    rw [indexedFamily_coboundary1]
    rfl
  rw [hin] at hs
  exact hs

/-- The empty physical prefix has zero actual FIRST, while its original
non-normalized Cx correction is retained. -/
theorem physicalReadout_one_zero (S : OddScale) : physicalReadout S 1 0=0 := by
  rw [physicalReadout_one]
  exact BDL26RXErrorPullback.zero_run_coarse S 3 rxIndex rxIndex_even

private abbrev P := (state witnessScale 2).presentation
private abbrev Data := BDL26RXDecoderAdapter.rxData witnessScale 3 rxIndex rxIndex_even
private abbrev Lq := BDL26RXDecoderAdapter.rxLq witnessScale 3 rxIndex rxIndex_even
private abbrev Syn := (indexedFamily witnessScale 3).Syndrome rxIndex.succ

/-- The original selected Cq component in raw graph coordinates. -/
def selectedQWord (sigma : Syn) (q : P.Q) :
    Word F (QDoubleCylinderVertex P q witnessScale) :=
  (wordEquiv (BDL26RXDecoderAdapter.qCorrectionEquiv P witnessScale q)).symm
    (restrictWordLinear (Lq.correctionRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q))

private theorem selected_q_delta (sigma : Syn) (q : P.Q)
    (g : Word F (QDoubleCylinderVertex P q witnessScale))
    (hinput : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
      (selectedQWord sigma q)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CqLocalRangeAt Data sigma.val q :=
    ⟨wordEquiv (qCorrectionEquiv P witnessScale q) g,
      (local_q_transport P witnessScale q g).trans hinput.symm⟩
  have hd := RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal_local_delta
    Data sigma.val q hrange
  have hlocal : wordLinearMapTranspose (localCq P witnessScale q).boundary2
      (restrictWordLinear ((localQ P witnessScale).correctionRegion q)
        (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q))=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g) :=
    hd.trans hinput
  have hs : selectedQWord sigma q=
      (wordEquiv (qCorrectionEquiv P witnessScale q)).symm
        (restrictWordLinear ((localQ P witnessScale).correctionRegion q)
          (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)) := by
    funext v
    rfl
  rw [hs]
  exact raw_q_delta P witnessScale q
    (restrictWordLinear ((localQ P witnessScale).correctionRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)) g hlocal

/-- Actual selected-word forcing. The sole hypothesis specifies the computed
cleaned input; both its range and the unchanged selector's budget are derived
here, rather than supplied as a selected correction certificate. -/
theorem selectedQWord_forced (sigma : Syn) (q : P.Q) (b : F)
    (hinput : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=
      wordEquiv (BDL26RXDecoderAdapter.qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
          (qPortWord P q b))) :
    selectedQWord sigma q (0,Sum.inl (Sum.inl ()))=b := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CqLocalRangeAt Data sigma.val q := by
    exact ⟨wordEquiv (qCorrectionEquiv P witnessScale q) (qPortWord P q b),
      (local_q_transport P witnessScale q (qPortWord P q b)).trans hinput.symm⟩
  apply q_branch_forced P (state witnessScale 2).admissible.toTannerSquareAdmissible q b
    (selectedQWord sigma q)
  · exact selected_q_delta sigma q (qPortWord P q b) hinput
  · have hw := RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal_local_flow_weight Data sigma.val q hrange
    change HammingWeight (BDL26RXDecoderAdapter.qFlow P witnessScale q
      (selectedQWord sigma q)) ≤ _ at hw
    rw [hinput] at hw
    exact hw.trans_eq (BDL26RXDecoderAdapter.wordEquiv_weight
      (BDL26RXDecoderAdapter.qSyndromeEquiv P witnessScale q) _)


private abbrev Lx := BDL26RXDecoderAdapter.rxLx witnessScale 3 rxIndex rxIndex_even

/-- Zero X input forces zero GLOBAL differential of every original Cx component.
The selected correction itself need not vanish. -/
theorem zero_x_component_boundary (sigma : Syn) (x : P.X)
    (hx : restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=0 := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CxLocalRangeAt Data sigma.val x := by
    change restrictWordLinear (Lx.syndromeRegion x) sigma.val∈_
    rw [hx]
    exact ⟨0,map_zero _⟩
  let f := restrictWordLinear (Lx.correctionRegion x)
    (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)
  have hlocal : Data.contract.rx_local_complexes.cxDelta1 x f=0 :=
    (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal_local_delta Data sigma.val x hrange).trans hx
  have hflow : Data.contract.support_decomposition.cxFlow x f=0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    have hw := RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal_local_flow_weight Data sigma.val x hrange
    rw [hx,HammingWeight_zero] at hw
    exact Nat.le_zero.mp hw
  have hb : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=
      (fun p : RX2 P witnessScale => extendWordLinear (Lx.syndromeRegion x)
        (Data.contract.rx_local_complexes.cxDelta1 x f) p+
        Data.contract.support_decomposition.cxFlow x f p) :=
    x_component_boundary witnessScale 3 rxIndex rxIndex_even sigma.val x
  exact hb.trans (by
    funext p
    rw [hlocal,hflow,map_zero]
    change (0:F)+0=0
    exact add_zero 0)

/-- Every original Cx component remains present. Its global cocycle equation,
derived above from the original budget, proves the cleaned Q input is unchanged. -/
theorem zero_x_cleaned_input (sigma : Syn)
    (hx : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val=sigma.val := by
  have hc : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxCorrectionTotal Data sigma.val)=0 := by
    change (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (∑ x,RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun x _ => zero_x_component_boundary sigma x (hx x))
  change sigma.val+(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
    (RXCoarseGraining.RXCoarseGrainingData.cxCorrectionTotal Data sigma.val)=sigma.val
  rw [hc,add_zero]


/-- Every Q block with zero cleaned input has zero ACTUAL outgoing flow.
No zero value is assumed for the selected correction word. -/
theorem selectedQWord_flow_zero (sigma : Syn) (q : P.Q)
    (hq : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=0) :
    BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)=0 := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CqLocalRangeAt Data sigma.val q := by
    change restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)∈_
    rw [hq]
    exact ⟨0,map_zero _⟩
  apply (HammingWeight_eq_zero_iff _).mp
  have hw := RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal_local_flow_weight Data sigma.val q hrange
  change HammingWeight (BDL26RXDecoderAdapter.qFlow P witnessScale q
    (selectedQWord sigma q)) ≤ _ at hw
  rw [hq,HammingWeight_zero] at hw
  exact Nat.le_zero.mp hw

/-- At an original doubled-Z coordinate the complete selected Cq component
has exactly its outgoing flow. All auxiliary local-syndrome terms are zero
there by their actual constructor, not dropped by an external certificate. -/
theorem selectedQWord_boundary_old_z (sigma : Syn) (q : P.Q) (z : P.Z) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q) (Sum.inr (z,c))=
      BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
        (Sum.inr (z,c)) := by
  let f := restrictWordLinear (Lq.correctionRegion q)
    (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)
  have hb : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)=
      (fun p : RX2 P witnessScale => extendWordLinear (Lq.syndromeRegion q)
        (Data.contract.rx_local_complexes.cqDelta1 q f) p+
        BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q) p) :=
    q_component_boundary witnessScale 3 rxIndex rxIndex_even sigma.val q
  have he := congrArg (fun w : Word F (RX2 P witnessScale) => w (Sum.inr (z,c))) hb
  have hout : Sum.inr (z,c)∉Lq.syndromeRegion q := by
    change Sum.inr (z,c)∉(localQ P witnessScale).syndromeRegion q
    exact old_z_not_q_region P witnessScale q z c
  have hz : extendWordLinear (Lq.syndromeRegion q)
      (Data.contract.rx_local_complexes.cqDelta1 q f) (Sum.inr (z,c))=0 :=
    dif_neg hout
  exact he.trans (by rw [hz,zero_add])

/-- The original coarse coordinate is doubled-Z COPY ZERO, retaining all
selected Q components. This is not the parity of the two physical copies. -/
theorem original_coarse_old_z (sigma : Syn) (z : P.Z)
    (hx : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even sigma).coarse.val z=
      sigma.val (Sum.inr (z,0))+
        ∑ q : P.Q,BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
          (Sum.inr (z,0)) := by
  rw [BDL26RXDecoderAdapter.rxStepOutput_coarse]
  change (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCq Data sigma.val) (Sum.inr (z,0))=_
  unfold RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCq
  rw [zero_x_cleaned_input sigma hx]
  change sigma.val (Sum.inr (z,0))+
    ((indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (∑ q : P.Q,RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)) (Sum.inr (z,0))=_
  have hmap : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (∑ q : P.Q,RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)=
      ∑ q : P.Q,(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
        (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q) :=
    map_sum _ _ _
  have hsum :
      (∑ q : P.Q,(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
        (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q))
          (Sum.inr (z,0))=
      ∑ q : P.Q,(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
        (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)
          (Sum.inr (z,0)) :=
    eval_sum _ _
  have hterms : (∑ q : P.Q,(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)
        (Sum.inr (z,0)))=
      ∑ q : P.Q,BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
        (Sum.inr (z,0)) :=
    Finset.sum_congr rfl (fun q _ => selectedQWord_boundary_old_z sigma q z 0)
  exact (congrArg (fun w : Word F (RX2 P witnessScale) =>
      sigma.val (Sum.inr (z,0))+w (Sum.inr (z,0))) hmap).trans
    (congrArg (fun r : F => sigma.val (Sum.inr (z,0))+r) (hsum.trans hterms))


/-- Only the local-X part of the coboundary is used as a physical error.
It is not the full global coboundary, which would have zero syndrome. -/
def gradientError (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    Word F (Physical witnessScale 3) :=
  xExtend P witnessScale x
    (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g)

def gradientInput (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) : Syn :=
  BDL26RXErrorPullback.errorSyndrome witnessScale 3 rxIndex (gradientError x g)

/-- The actual full syndrome of this local gradient is exactly its outgoing
X-to-Q flow. In particular it has neither an X part nor a doubled-Z part. -/
theorem gradientInput_value (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    (gradientInput x g).val=xFlow P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g) := by
  change (indexedFamily witnessScale 3).coboundary1 rxIndex.succ (gradientError x g)=_
  rw [indexedFamily_coboundary1]
  change tannerCoboundary1 (rxReplacementPresentation P witnessScale)
    (xExtend P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g))=_
  rw [rxPresentation_coboundary1_eq P (state witnessScale 2).admissible
    (state witnessScale 2).regular witnessScale]
  change BDL26ReplacementCochainMaps.rxCoboundary1 P witnessScale
    (xExtend P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g))=_
  rw [xDelta1_decomposition]
  have hz : wordLinearMapTranspose (doubleCylinderBoundary2 P x witnessScale)
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g)=0 :=
    LinearMap.congr_fun (doubleCylinderCoboundary_squared P x witnessScale) g
  rw [hz,map_zero,zero_add]

theorem gradientInput_x_zero (x y : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    restrictWordLinear (Lx.syndromeRegion y) (gradientInput x g).val=0 := by
  funext j
  obtain ⟨face,rfl⟩ := (xSyndromeEquiv P witnessScale y).surjective j
  change (gradientInput x g).val (Sum.inl (Sum.inl ⟨y,face⟩))=0
  rw [gradientInput_value,xFlow_at_x]

theorem gradientInput_old_z_zero (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (z : P.Z) (c : BDL26FiniteTannerSquare.Two) :
    (gradientInput x g).val (Sum.inr (z,c))=0 := by
  rw [gradientInput_value,xFlow_at_z]

/-- Exact actual cleaned input at every incident Q block. -/
theorem gradientInput_q (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale))
    (q : P.Q) (hxq : P.xq x q=true) :
    restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data (gradientInput x g).val)=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
          (rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
            q x hxq witnessScale g)) := by
  rw [zero_x_cleaned_input (gradientInput x g) (gradientInput_x_zero x · g)]
  funext j
  obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P witnessScale q).surjective j
  change (gradientInput x g).val (Sum.inl (Sum.inr ⟨q,edge⟩))=_
  exact (congrFun (gradientInput_value x g) (Sum.inl (Sum.inr ⟨q,edge⟩))).trans
    ((x_flow_gradient_at_q P (state witnessScale 2).admissible.toTannerSquareAdmissible
      witnessScale x g q edge hxq).trans
        (word_equiv_forward_apply (qSyndromeEquiv P witnessScale q) _ edge).symm)

/-- All off-face Q components have zero outgoing flow by the actual budget. -/
theorem gradientInput_other_q_flow_zero (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (q : P.Q)
    (hxq : P.xq x q≠true) :
    qFlow P witnessScale q (selectedQWord (gradientInput x g) q)=0 := by
  apply selectedQWord_flow_zero
  rw [zero_x_cleaned_input (gradientInput x g) (gradientInput_x_zero x · g)]
  funext j
  obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P witnessScale q).surjective j
  change (gradientInput x g).val (Sum.inl (Sum.inr ⟨q,edge⟩))=0
  rw [gradientInput_value,xFlow_at_q P
    (state witnessScale 2).admissible.toTannerSquareAdmissible,dif_neg hxq]

/-- The previously proved budget now applies to the ACTUAL original selector,
with its cleaned input computed from the physical local gradient. -/
theorem gradientInput_root_forced (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (q : P.Q)
    (hxq : P.xq x q=true) (b : F)
    (hg : rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      q x hxq witnessScale g=qPortWord P q b) :
    selectedQWord (gradientInput x g) q (0,Sum.inl (Sum.inl ()))=b := by
  apply selectedQWord_forced
  rw [gradientInput_q x g q hxq,hg]


/-- Reindexing of the original selected Q equation for any actual cleaned
local graph input, including the mixed-port cases with multiple budget choices. -/
theorem selectedQWord_delta (sigma : Syn) (q : P.Q)
    (g : Word F (QDoubleCylinderVertex P q witnessScale))
    (hinput : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
      (selectedQWord sigma q)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g := by
  exact selected_q_delta sigma q g hinput

/-- The bit is the literal C2 Z-cylinder copy tag. -/
def zCopyBit (z : P.Z) : F := if z.2.1=0 then 0 else 1

/-- Independent copy bits at Q vertices; copy-invariant bits at Z vertices.
Every coefficient is internally defined on the full actual X cylinder. -/
def splitPotential (x : P.X) : Word F (DoubleCylinderVertex P x witnessScale) := fun v =>
  match v.2 with
  | Sum.inl w => match w.1 with
    | Vertex.q _ => if v.1=0 then 0 else 1
    | Vertex.z z => zCopyBit z
    | Vertex.x _ => 0
  | _ => 0

private theorem splitPotential_q_root (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (c : BDL26FiniteTannerSquare.Two) :
    rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      q x hxq witnessScale (splitPotential x) (c,Sum.inl (Sum.inl ()))=
      if c=0 then 0 else 1 := rfl

private theorem splitPotential_q_leaf (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      q x hxq witnessScale (splitPotential x) (c,Sum.inl (Sum.inr z))=
      zCopyBit z.1 := rfl

/-- Actual root coefficients on the original face star; zero elsewhere. -/
def rootWord (x : P.X) : Word F P.Q := fun q =>
  if P.xq x q=true then
    selectedQWord (gradientInput x (splitPotential x)) q (0,Sum.inl (Sum.inl ()))
  else 0

/-- At every incident Q cylinder, all its selected leaf values are the same
original root coefficient plus the prescribed Z bit. This retains all ties. -/
theorem split_selected_leaf (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    selectedQWord (gradientInput x (splitPotential x)) q (c,Sum.inl (Sum.inr z))=
      rootWord x q+zCopyBit z.1 := by
  let g := rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
    q x hxq witnessScale (splitPotential x)
  have hd := selectedQWord_delta (gradientInput x (splitPotential x)) q g
    (gradientInput_q x (splitPotential x) q hxq)
  have hc := q_preimage_difference P (state witnessScale 2).admissible.toTannerSquareAdmissible
    witnessScale q g (selectedQWord (gradientInput x (splitPotential x)) q)
    hd.symm (c,Sum.inl (Sum.inr z))
  change _+zCopyBit z.1=
    selectedQWord (gradientInput x (splitPotential x)) q (0,Sum.inl (Sum.inl ()))+0 at hc
  rw [add_zero] at hc
  have ht := congrArg (fun r : F => r+zCopyBit z.1) hc
  rw [add_assoc,ZModModule.add_self,add_zero] at ht
  simpa only [rootWord,if_pos hxq] using ht

/-- The internally constructed root word has exact original face-star support. -/
theorem rootWord_supported (x : P.X) :
    hammingSupport (rootWord x)⊆BDL26RXPhysicalStarTransport.physicalXStar P x := by
  exact incident_word_supported P x (fun q =>
    selectedQWord (gradientInput x (splitPotential x)) q (0,Sum.inl (Sum.inl ())))


private theorem split_q_flow (x : P.X) (q : P.Q) (z : P.Z) :
    qFlow P witnessScale q (selectedQWord (gradientInput x (splitPotential x)) q)
      (Sum.inr (z,0))=
      rootWord x q*(if P.qz q z=true then 1 else 0)+
        zCopyBit z*(if P.xq x q=true then 1 else 0)*
          (if P.qz q z=true then 1 else 0) := by
  by_cases hxq : P.xq x q=true
  · rw [qFlow_at_z]
    by_cases hqz : P.qz q z=true
    · change (BDL26ReplacementSupport.rxQOutgoing P q witnessScale
        (selectedQWord (gradientInput x (splitPotential x)) q) z) 0=_
      rw [BDL26ReplacementSupport.rxQOutgoing,dif_pos hqz]
      change selectedQWord (gradientInput x (splitPotential x)) q
        (0,Sum.inl (Sum.inr ⟨z,hqz⟩))=_
      rw [split_selected_leaf x q hxq ⟨z,hqz⟩ 0]
      simp only [if_pos hqz,if_pos hxq,mul_one]
    · rw [BDL26ReplacementSupport.rxQOutgoing_nonincident P q witnessScale _ z hqz]
      simp only [Pi.zero_apply,if_neg hqz,mul_zero,add_zero]
  · rw [gradientInput_other_q_flow_zero x (splitPotential x) q hxq]
    simp only [Pi.zero_apply,rootWord,if_neg hxq,zero_mul,add_zero,mul_zero]

/-- The complete actual coarse output is the syndrome of the derived root
word. The prescribed Z bits cancel by the original Tanner coboundary-square
identity, not by summing the two physical output copies. -/
theorem split_coarse_eq_root_syndrome (x : P.X) :
    (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even
      (gradientInput x (splitPotential x))).coarse.val=tannerCoboundary1 P (rootWord x) := by
  funext z
  rw [original_coarse_old_z _ z (gradientInput_x_zero x · (splitPotential x)),
    gradientInput_old_z_zero,zero_add]
  calc
    _ = ∑ q : P.Q,(rootWord x q*(if P.qz q z=true then 1 else 0)+
        zCopyBit z*(if P.xq x q=true then 1 else 0)*
          (if P.qz q z=true then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact split_q_flow x q z
    _ = tannerCoboundary1 P (rootWord x) z :=
      shifted_tanner_syndrome P x (rootWord x) (zCopyBit z) z

/-- Every physical flip in the full local-gradient word is a literal seed of
this face's original tower. No arbitrary owner is substituted for the face. -/
theorem gradientError_tower_support (z : (RawOne witnessScale).Z)
    (f : ZDoubleCylinderFace (RawOne witnessScale) z witnessScale)
    (g : Word F (DoubleCylinderVertex P
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale))
    (q : Physical witnessScale 3)
    (hq : q∈hammingSupport
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) g)) :
    Nonempty (BDL26RXFaceEdgeTower.Tower witnessScale 1 q) := by
  rcases q with ⟨y,e⟩ | ⟨r,v⟩
  · have hy : y=BDL26RXFaceEdgeTower.faceOwner witnessScale z f := by
      by_contra hn
      have hz := xExtend_other P witnessScale
        (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) y hn
        (wordLinearMapTranspose (doubleCylinderBoundary1 P
          (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale) g) e
      exact (Finset.mem_filter.mp hq).2 hz
    subst y
    have he : BDL26RXFaceEdgeTower.seedPhysical witnessScale ⟨z,f,e⟩=
        Sum.inl ⟨BDL26RXFaceEdgeTower.faceOwner witnessScale z f,e⟩ := rfl
    rw [←he]
    exact ⟨BDL26RXFaceEdgeTower.Tower.seed ⟨z,f,e⟩⟩
  · have hz := xExtend_at_q P witnessScale
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z f)
      (wordLinearMapTranspose (doubleCylinderBoundary1 P
        (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale) g) r v
    exact False.elim ((Finset.mem_filter.mp hq).2 hz)


private theorem sum_on_image {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (embed : I → J) (hi : Function.Injective embed) (f : J → F)
    (hz : ∀ j, j∉Finset.univ.image embed → f j=0) :
    (∑ j,f j)=∑ i,f (embed i) := by
  calc
    _ = ∑ j∈Finset.univ.image embed,f j := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hz j hj)
    _ = _ := Finset.sum_image (fun i _ j _ h => hi h)

/-- On the literal isolated four-edge rectangle, closedness forces the two
end-copy edge coefficients equal. No assertion of this form is made for a
general graph; the support assumption contains exactly the actual four slots. -/
theorem rectangle_closed_end_copies (T : TannerSquarePresentation) (x : T.X)
    (S : OddScale) (rect : SubdivisionBoundaryEdge T x S)
    (w : Word F (DoubleCylinderEdge T x S))
    (hs : hammingSupport w⊆Finset.univ.image
      (doubleCylinderRectangleBoundaryEdge T x S rect))
    (hc : doubleCylinderBoundary1 T x S w=0) :
    w (Sum.inl (0,rect.1))=w (Sum.inl (1,rect.1)) := by
  have hread : ∀ c : BDL26FiniteTannerSquare.Two,
      doubleCylinderBoundary1 T x S w
        (c,(subdivisionBoundaryEdgeStart T x S rect).1)=
        w (Sum.inl (c,rect.1))+w (Sum.inr (subdivisionBoundaryEdgeStart T x S rect)) := by
    intro c
    change (∑ edge,doubleCylinderEdgeVertexMatrix T x S
      (c,(subdivisionBoundaryEdgeStart T x S rect).1) edge*w edge)=_
    rw [sum_on_image (doubleCylinderRectangleBoundaryEdge T x S rect)
      (doubleCylinderRectangleBoundaryEdge_injective T x S rect)]
    · have hne := subdivisionEdgeStart_ne_end T x S rect.1
      fin_cases c <;>
        simp [Fintype.sum_prod_type,Fin.sum_univ_two,doubleCylinderRectangleBoundaryEdge,
          doubleCylinderEdgeVertexMatrix,subdivisionEdgeVertexMatrix,
          subdivisionBoundaryEdgeStart_value,subdivisionBoundaryEdgeEnd_value,
          hne]
    · intro edge hedge
      have hw : w edge=0 := by
        by_contra hn
        exact hedge (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
      rw [hw,mul_zero]
  have h0 := (hread 0).symm.trans (congrFun hc
    (0,(subdivisionBoundaryEdgeStart T x S rect).1))
  have h1 := (hread 1).symm.trans (congrFun hc
    (1,(subdivisionBoundaryEdgeStart T x S rect).1))
  exact add_right_cancel (h0.trans h1.symm)

private abbrev One := RawOne witnessScale
private abbrev OneA := (rxState witnessScale baseState).admissible

/-- End-copy edges of an actual C2 Z-cylinder rectangle. -/
def rectangleEndEdge (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale)
    (c : BDL26FiniteTannerSquare.Two) : P.Q := Sum.inl ⟨z,Sum.inl (c,rect.1)⟩

private theorem rectangleEndEdge_incident (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) (c : BDL26FiniteTannerSquare.Two) :
    P.xq (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (rectangleEndEdge z rect c)=true := by
  change rzXQIncidence One OneA.toTannerSquareAdmissible witnessScale
    (Sum.inl (Sum.inl ⟨z,Sum.inr rect⟩)) (Sum.inl ⟨z,Sum.inl (c,rect.1)⟩)=true
  apply decide_eq_true
  refine ⟨rfl,?_⟩
  exact (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
    (transposePresentation One) z witnessScale _ rect).mpr
      ⟨(0,c),doubleCylinderRectangleBoundaryEdge_zero _ _ _ _ _⟩

/-- Every Z neighbor of an actual end-copy edge has that same original copy.
This is derived from the original RZ incidence matrix, without an endpoint list
supplied by the caller. -/
private theorem rectangleEndEdge_neighbor_copy (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale)
    (c : BDL26FiniteTannerSquare.Two) (v : QStarEdge P (rectangleEndEdge z rect c)) : v.1.2.1=c := by
  rcases v with ⟨⟨z',⟨d,vertex⟩⟩,hv⟩
  change rzQZIncidence One OneA.toTannerSquareAdmissible witnessScale
    (Sum.inl ⟨z,Sum.inl (c,rect.1)⟩) ⟨z',(d,vertex)⟩=true at hv
  obtain ⟨htag,hm⟩ := of_decide_eq_true hv
  cases htag
  by_contra hn
  have hz : doubleCylinderEdgeVertexMatrix (transposePresentation One) z witnessScale
      (d,vertex) (Sum.inl (c,rect.1))=0 := by
    simp only [doubleCylinderEdgeVertexMatrix,if_neg hn]
  exact zero_ne_one (hz.symm.trans hm)

private theorem rectangleEndEdge_split (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) (c : BDL26FiniteTannerSquare.Two) :
    rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      (rectangleEndEdge z rect c)
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (rectangleEndEdge_incident z rect c) witnessScale
      (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect)))=
      qPortWord P (rectangleEndEdge z rect c) (if c=0 then 0 else 1) := by
  funext v
  rcases v with ⟨d,v⟩
  rcases v with (root|port)|⟨port,j⟩
  · cases root
    exact splitPotential_q_root _ _ _ d
  · rw [splitPotential_q_leaf,qPortWord_leaf]
    simp only [zCopyBit,rectangleEndEdge_neighbor_copy z rect c port]
  · exact Fin.elim0 j

/-- The two opposite actual boundary edges have FORCED DIFFERENT root bits,
for every original admissible Cq correction and every possible mixed-edge tie. -/
theorem rectangle_root_end_copies (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) (c : BDL26FiniteTannerSquare.Two) :
    rootWord (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (rectangleEndEdge z rect c)=(if c=0 then 0 else 1) := by
  rw [rootWord,if_pos (rectangleEndEdge_incident z rect c)]
  exact gradientInput_root_forced _ _ _ (rectangleEndEdge_incident z rect c) _
    (rectangleEndEdge_split z rect c)


/-- Exact four-slot support and actual RZ local cycle equations rule out a
closed root word: its two end-copy coefficients were forced to be 0 and 1. -/
theorem rectangle_root_nonclosed (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) :
    tannerCoboundary1 P
      (rootWord (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect)))≠0 := by
  let x := BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect)
  intro hc
  have hq : ∀ q v,rootWord x (Sum.inr ⟨q,v⟩)=0 := by
    intro q v
    change (if rzXQIncidence One OneA.toTannerSquareAdmissible witnessScale
      (Sum.inl (Sum.inl ⟨z,Sum.inr rect⟩)) (Sum.inr ⟨q,v⟩)=true then _ else 0)=0
    simp only [rzXQIncidence,Bool.false_eq_true,if_false]
  have hraw : BDL26ReplacementCochainMaps.rzCoboundary1 One OneA witnessScale (rootWord x)=0 := hc
  have hcycle := rzLocal_cycle_of_cocycle_q_zero One OneA witnessScale
    (rootWord x) hraw hq z
  have hs : hammingSupport (fun edge => rootWord x (Sum.inl ⟨z,edge⟩))⊆
      Finset.univ.image (doubleCylinderRectangleBoundaryEdge
        (transposePresentation One) z witnessScale rect) := by
    apply support_subset_of_nonzero
    intro edge hn
    have hi : P.xq x (Sum.inl ⟨z,edge⟩)=true := by
      by_contra hnot
      apply hn
      simp only [rootWord,if_neg hnot]
    change rzXQIncidence One OneA.toTannerSquareAdmissible witnessScale
      (Sum.inl (Sum.inl ⟨z,Sum.inr rect⟩)) (Sum.inl ⟨z,edge⟩)=true at hi
    obtain ⟨htag,hm⟩ := of_decide_eq_true hi
    change doubleCylinderFaceEdgeMatrix (transposePresentation One) z witnessScale
      edge (Sum.inr rect)=1 at hm
    obtain ⟨slot,hslot⟩ := (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
      (transposePresentation One) z witnessScale edge rect).mp hm
    exact Finset.mem_image.mpr ⟨slot,Finset.mem_univ _,hslot⟩
  have heq := rectangle_closed_end_copies (transposePresentation One) z witnessScale rect
    (fun edge => rootWord x (Sum.inl ⟨z,edge⟩)) hs hcycle
  change rootWord x (rectangleEndEdge z rect 0)=rootWord x (rectangleEndEdge z rect 1) at heq
  rw [rectangle_root_end_copies,rectangle_root_end_copies] at heq
  change (0:F)=1 at heq
  exact zero_ne_one heq

/-- Nonzero ACTUAL original coarse readout, with the complete physical error
and all original Cx/Cq choices retained. The endpoint is constructed internally. -/
theorem rectangle_physical_readout_nonzero (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) :
    physicalReadout witnessScale 1
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
        (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))))≠0 := by
  rw [physicalReadout_one]
  change (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even
    (gradientInput (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))))).coarse.val≠0
  rw [split_coarse_eq_root_syndrome]
  exact rectangle_root_nonclosed z rect

private def witnessOldFace : One.Face := Sum.inr (Sum.inr ((0 : BDL26FiniteTannerSquare.BaseFace),(0 : BDL26FiniteTannerSquare.Two)))
private def witnessZ : One.Z := One.faceZ witnessOldFace

private def faceBoundaryStarEdge (T : TannerSquarePresentation) (f : T.Face) :
    XStarBoundaryEdge T (T.faceX f) :=
  ⟨Sum.inr (faceQZEdge T f 0),by
    change decide (∃ g : T.Face,
      xStarFaceMember T (T.faceX f) g=true ∧
      decide (faceQZEdge T f 0=faceQZEdge T g 0 ∨
        faceQZEdge T f 0=faceQZEdge T g 1)=true)=true
    apply decide_eq_true
    refine ⟨f,?_,?_⟩
    · change decide (T.faceX f=T.faceX f)=true
      exact decide_eq_true rfl
    · exact decide_eq_true (Or.inl rfl)⟩

private def witnessBoundaryStarEdge : XStarBoundaryEdge (transposePresentation One) witnessZ :=
  faceBoundaryStarEdge (transposePresentation One) witnessOldFace

private def witnessRectangle : SubdivisionBoundaryEdge (transposePresentation One) witnessZ witnessScale :=
  subdivisionOriginalBoundaryEdge (transposePresentation One) witnessZ witnessScale
    witnessBoundaryStarEdge ⟨0,by decide⟩

/-- Actual existential readout classification. The witness has the same
original fixed n=1 throughout. Its input is built from a physical prefix; the
next flip is a literal original face-edge seed, and SECOND is the unchanged
original readout after that physical translation. -/
theorem exists_first_zero_second_nonzero :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2)),
      Nonempty (BDL26RXFaceEdgeTower.Tower S n q) ∧
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 := by
  let x := BDL26RXFaceEdgeTower.faceOwner witnessScale witnessZ (Sum.inr witnessRectangle)
  let e := gradientError x (splitPotential x)
  have hzero : physicalReadout witnessScale 1 0=0 := physicalReadout_one_zero witnessScale
  have hne : physicalReadout witnessScale 1 e≠0 :=
    rectangle_physical_readout_nonzero witnessZ witnessRectangle
  obtain ⟨a,q,hq,ha,hb⟩ := physical_crossing witnessScale 1 e hzero hne
  refine ⟨witnessScale,1,physicalInput witnessScale 1 a,q,?_,ha,hb⟩
  exact gradientError_tower_support witnessZ (Sum.inr witnessRectangle) (splitPotential x) q hq


/-- The nonzero SECOND has an independently returned original search word and
an actually nonzero correction. Nonzeroness follows from the original syndrome
equation; it is not stored as a premise of a witness structure. -/
theorem nonzero_second_returned (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : BDL26RXFaceEdgeTower.Tower S n q)
    (hfirst : firstReadout S n u=0) (hsecond : secondReadout S n u q≠0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 := by
  obtain ⟨w,hw,he,hl,hd⟩ := BDL26RXFaceEdgeTower.second_returned S n u q t hfirst
  refine ⟨w,hw,he,hl,hd,?_⟩
  intro hz
  apply hsecond
  exact hd.symm.trans ((congrArg (BDL26RXFaceEdgeTower.delta S) hz).trans (map_zero _))

/-- Whole actual witness consumer: original FIRST and SECOND, returned search
word, nonzero selected correction, BOTH literal base calls, and the full Phi
formula and original top correction equation all share the same S,n,u,q. -/
theorem exists_complete_original_witness :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2))
      (t : BDL26RXFaceEdgeTower.Tower S n q)
      (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S)),
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 ∧
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 ∧
      (SuffixData S n).family.coboundary0 0 (BDL26RXFaceEdgeTower.basePotential S n u q t)=
        (descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26RXFaceEdgeTower.fullPotential S n u q t=
        intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (BDL26RXFaceEdgeTower.basePotential S n u q t)+accumulated S n u q ∧
      (SuffixData S n).family.coboundary0 (TopIndex n)
        (BDL26RXFaceEdgeTower.fullPotential S n u q t)=
        BDL26ActualFailureReadout.flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (BDL26ActualFailureReadout.flip S n q)) := by
  obtain ⟨S,n,u,q,⟨t⟩,hfirst,hsecond⟩ := exists_first_zero_second_nonzero
  obtain ⟨w,hw,he,hl,hd,hn⟩ := nonzero_second_returned S n u q t hfirst hsecond
  exact ⟨S,n,u,q,t,w,hfirst,hsecond,hw,he,hl,hd,hn,
    BDL26RXFaceEdgeTower.base_history_spec S n u q t hfirst,
    BDL26RXFaceEdgeTower.full_potential_formula S n u q t,
    BDL26RXFaceEdgeTower.original_correction_equation S n u q t hfirst⟩

end QEC.Coding.BDL26RXFaceSecondReadout
