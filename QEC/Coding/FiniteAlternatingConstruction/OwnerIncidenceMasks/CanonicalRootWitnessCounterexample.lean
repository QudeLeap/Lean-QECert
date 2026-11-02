import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformIsolation

/-!
# Nonboundary witness for the canonical original root component

At every odd scale, a valid syndrome with nonzero stopped base input has a
top witness selected by the original marked root component outside the full
top coboundary range. The construction uses the canonical decoder, graph,
marks and actual history stopped at physical C2.
-/
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators

noncomputable section

/-- A single view of the exact family consumed by the actual decoder. -/
abbrev CF (S : OddScale) := (indexedDecoderData S 4).family
abbrev level3 : LevelIndex 4 := (2 : StepIndex 4).succ
abbrev level4 : LevelIndex 4 := (3 : StepIndex 4).succ

/-- Typed graph constructors avoid inferring a recursive presentation through
an implicit constructor parameter. These are the original vertices. -/
def zVertex (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    GraphVertex S (n+1) := @Vertex.z (state S n).presentation z

/-- Literal Sigma nodes on the original graph, with their levels fixed once. -/
def actualTopNode (S : OddScale) (v : GraphVertex S 4) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(4 : LevelIndex 4),v⟩
def actualMidNode (S : OddScale) (v : GraphVertex S 3) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(3 : LevelIndex 4),v⟩
def actualBaseNode (S : OddScale) (v : GraphVertex S 2) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(2 : LevelIndex 4),v⟩

/-- Exact original constructor interfaces. Their ordinary def heads protect
implicit matching; these equations expose only the one requested node. -/
private theorem zVertex_eq (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    zVertex S n z = @Vertex.z (state S n).presentation z := rfl
private theorem actualTopNode_physical (S : OddScale) (v : GraphVertex S 4) :
    actualTopNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) v := rfl
private theorem actualMidNode_physical (S : OddScale) (v : GraphVertex S 3) :
    actualMidNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : LevelIndex 2) v := rfl
private theorem actualBaseNode_physical (S : OddScale) (v : GraphVertex S 2) :
    actualBaseNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : LevelIndex 2) v := rfl

/-- One literal adjacent-level chart for each owned node.  These expose only
Sigma/Fin constructors; no graph, history, root predicate or mark is evaluated. -/
private theorem actualTopNode_literal (S : OddScale) (v : GraphVertex S 4) :
    actualTopNode S v =
      (⟨(3 : StepIndex 4).succ,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl
private theorem actualMidNode_literal (S : OddScale) (v : GraphVertex S 3) :
    actualMidNode S v =
      (⟨(2 : StepIndex 4).succ,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl
private theorem actualMidNode_castSucc_literal (S : OddScale) (v : GraphVertex S 3) :
    actualMidNode S v =
      (⟨(3 : StepIndex 4).castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl
private theorem actualBaseNode_literal (S : OddScale) (v : GraphVertex S 2) :
    actualBaseNode S v =
      (⟨(2 : StepIndex 4).castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl

abbrev Word3 (S : OddScale) := (CF S).Cochain2 level3
abbrev Correction3 (S : OddScale) := (CF S).Cochain1 level3
noncomputable abbrev A (S : OddScale) := rxData S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev LX (S : OddScale) := rxLx S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev LQ (S : OddScale) := rxLq S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev d3 (S : OddScale) := (CF S).coboundary1 level3

private theorem CF_coboundary1 (S : OddScale) (i : LevelIndex 4) :
    (CF S).coboundary1 i = BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S i.val).presentation :=
  indexedFamily_coboundary1 S 4 i

/-- A term-level finite-sum elimination, on its exact binder and instances. -/
private theorem sum_single_value {I : Type} [Fintype I] [DecidableEq I]
    (f : I → BDL26Field) (a : I) (hz : ∀ b, b ≠ a → f b = 0) :
    (∑ b, f b) = f a := by
  exact Finset.sum_eq_single a (fun b _hb hba => hz b hba) (by simp)

private theorem mask_filter_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Prop) [DecidablePred P] (word : I → BDL26Field) (p : I) :
    maskWord (Finset.univ.filter P) word p = if P p then word p else 0 := by
  simp only [maskWord,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem extend_restrict_eq {T : Type} [Fintype T] [DecidableEq T]
    (R : Finset T) (w : Word BDL26Field T) (hw : ∀ p, p ∉ R → w p = 0) :
    extendWordLinear R (restrictWordLinear R w) = w := by
  ext p
  change (if h : p ∈ R then w p else 0) = w p
  by_cases hp : p ∈ R
  · simp only [dif_pos hp]
  · simp only [dif_neg hp, hw p hp]

/-- Term-level restriction on an arbitrary carrier; no closed record is reduced. -/
private theorem restriction_zero_of_values {I : Type} [Fintype I] [DecidableEq I]
    (R : Finset I) (word : I → BDL26Field) (hz : ∀ p, p ∈ R → word p = 0) :
    restrictWordLinear R word = 0 := by
  funext p
  exact hz p.val p.property

/-- Isolation is proved on abstract nodes and relations before applying it to
any actual canonical history. The relation and original endpoints are retained. -/
private theorem no_path_of_no_outgoing {N : Type} (R : N → N → Prop)
    (a r : N) (hne : a ≠ r) (hout : ∀ w, ¬ R a w) :
    ¬ Relation.ReflTransGen R a r := by
  intro hpath
  rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
  · exact hne heq
  · exact hout next hedge

/-- A nonzero selected coordinate is sufficient to preserve its value, while
zero coordinates need no membership claim. The predicate stays abstract. -/
private theorem selected_value_eq {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : word p ≠ 0 → P p) :
    (if P p then word p else 0) = word p := by
  by_cases hz : word p = 0
  · by_cases hk : P p
    · exact if_pos hk
    · exact (if_neg hk).trans hz.symm
  · exact if_pos (hp hz)

/-- Equality transport is established on an abstract predicate before that
predicate is instantiated by a concrete actual root-component membership. -/
private theorem predicate_transport {N : Type} (P : N → Prop)
    {a b : N} (he : a = b) (hb : P b) : P a := by
  cases he
  exact hb

/-- A whole family of original nonzero guards preserves the same masked
values; no actual graph, selected word or indexed decoder enters this proof. -/
private theorem finite_indexed_guard_values {I N F : Type} [Zero F]
    (f : I → N) (w : N → F) (P : N → Prop) [DecidablePred P]
    (h : ∀ i, w (f i) ≠ 0 → P (f i)) :
    ∀ i, (if P (f i) then w (f i) else 0) = w (f i) := by
  intro i
  by_cases hz : w (f i) = 0
  · rw [hz]
    split_ifs <;> rfl
  · exact if_pos (h i hz)

/-- Coordinate evaluation of equal subtype words without specifying either
closed family record in the congrArg binder. -/
private theorem subtype_coordinate_eq {I : Type} {P : (I → BDL26Field) → Prop}
    {a b : {word : I → BDL26Field // P word}} (he : a = b) (p : I) :
    a.val p = b.val p :=
  congrArg (fun word : {w : I → BDL26Field // P w} => word.val p) he

/-- The existing coordinate mask as a generic function. It has no decoder,
finite graph, choice of root, or modified membership predicate. -/
private noncomputable def selectedWord {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) : I → BDL26Field :=
  fun p => if P p then word p else 0

private theorem selectedWord_apply {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) :
    selectedWord P word p = if P p then word p else 0 := rfl

private theorem selectedWord_zero {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : ¬ P p) : selectedWord P word p = 0 :=
  (selectedWord_apply P word p).trans (if_neg hp)

private theorem selectedWord_preserves {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : word p ≠ 0 → P p) :
    selectedWord P word p = word p :=
  (selectedWord_apply P word p).trans (selected_value_eq P word p hp)

/-- Whole-word masks are equal for pointwise equivalent predicates. Each
mask keeps its own original decision dictionary; only truth values are used. -/
private theorem selectedWord_congr_iff {I : Type} (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ p, P p ↔ Q p)
    (word : I → BDL26Field) : selectedWord P word = selectedWord Q word := by
  funext p
  by_cases hp : P p
  · have hq : Q p := (h p).mp hp
    simp only [selectedWord_apply,if_pos hp,if_pos hq]
  · have hq : ¬Q p := fun hq => hp ((h p).mpr hq)
    simp only [selectedWord_apply,if_neg hp,if_neg hq]

/-- Scalar mask interchange, allowing distinct original decision dictionaries.
All branching is performed on abstract propositions, never actual graph data. -/
private theorem conditional_swap (P Q : Prop)
    (dP : Decidable P) (dQ : Decidable Q) (dQ' : Decidable Q) (dP' : Decidable P)
    (a : BDL26Field) :
    @ite BDL26Field P dP (@ite BDL26Field Q dQ a 0) 0 =
      @ite BDL26Field Q dQ' (@ite BDL26Field P dP' a 0) 0 := by
  by_cases hp : P <;> by_cases hq : Q
  all_goals simp only [if_pos,if_neg,hp,hq]

/-- A zero local query forces the actual X *boundary* to vanish.
The actual chosen closed correction is retained and is not asserted zero. -/
theorem actual_cx_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (x : (state S 2).presentation.X) :
    d3 S (cxComponentTotal (A S) sigma x) = 0 := by
  classical
  have hr : CxLocalRangeAt (A S) sigma x := by
    change restrictWordLinear ((LX S).syndromeRegion x) sigma ∈ _
    rw [hx x]
    exact ⟨0, map_zero _⟩
  let f := restrictWordLinear ((LX S).correctionRegion x)
    (cxComponentTotal (A S) sigma x)
  have hext : extendWordLinear ((LX S).correctionRegion x) f =
      cxComponentTotal (A S) sigma x :=
    extend_restrict_eq _ _ (cxComponentTotal_supported (A S) sigma x)
  have hd : (A S).contract.rx_local_complexes.cxDelta1 x f = 0 := by
    exact (cxComponentTotal_local_delta (A S) sigma x hr).trans (hx x)
  have hw : HammingWeight ((A S).contract.support_decomposition.cxFlow x f) = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hx x, HammingWeight_zero] using
      cxComponentTotal_local_flow_weight (A S) sigma x hr
  have hf : (A S).contract.support_decomposition.cxFlow x f = 0 :=
    (HammingWeight_eq_zero_iff _).mp hw
  have hdec := (A S).contract.support_decomposition.cxDelta1_decomposition x f
  rw [hext, hd, hf, map_zero, zero_add] at hdec
  exact hdec

/-- The complete canonical X correction has zero boundary on zero X queries. -/
theorem actual_cx_total_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0) :
    d3 S (cxCorrectionTotal (A S) sigma) = 0 := by
  classical
  change d3 S (∑ x, cxComponentTotal (A S) sigma x) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun x _ => actual_cx_boundary_zero S sigma hx x)

/-- The corresponding fact for the actual Q selector after the actual X step. -/
theorem actual_cq_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = 0)
    (q : (state S 2).presentation.Q) :
    d3 S (cqComponentTotal (A S) sigma q) = 0 := by
  classical
  have hr : CqLocalRangeAt (A S) sigma q := by
    change restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) ∈ _
    rw [hq q]
    exact ⟨0, map_zero _⟩
  let f := restrictWordLinear ((LQ S).correctionRegion q)
    (cqComponentTotal (A S) sigma q)
  have hext : extendWordLinear ((LQ S).correctionRegion q) f =
      cqComponentTotal (A S) sigma q :=
    extend_restrict_eq _ _ (cqComponentTotal_supported (A S) sigma q)
  have hd : (A S).contract.rx_local_complexes.cqDelta1 q f = 0 := by
    exact (cqComponentTotal_local_delta (A S) sigma q hr).trans (hq q)
  have hw : HammingWeight ((A S).contract.support_decomposition.cqFlow q f) = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hq q, HammingWeight_zero] using
      cqComponentTotal_local_flow_weight (A S) sigma q hr
  have hf : (A S).contract.support_decomposition.cqFlow q f = 0 :=
    (HammingWeight_eq_zero_iff _).mp hw
  have hdec := (A S).contract.support_decomposition.cqDelta1_decomposition q f
  rw [hext, hd, hf, map_zero, zero_add] at hdec
  exact hdec

theorem actual_cq_total_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = 0) :
    d3 S (cqCorrectionTotal (A S) sigma) = 0 := by
  classical
  change d3 S (∑ q, cqComponentTotal (A S) sigma q) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun q _ => actual_cq_boundary_zero S sigma hq q)

/-- The original odd-input branch, with the actual decoder-family carrier.
This equality never changes a selected output. -/
private theorem selected_RX_eq (S : OddScale) :
    (indexedDecoderData S 4).selectedMap (2 : StepIndex 4) =
      (indexedDecoderData S 4).rxMap (2 : StepIndex 4) :=
  selectedMap_eq_rx_of_odd_input (indexedDecoderData S 4) (2 : StepIndex 4) (by decide)

/-- Diagonal evaluation as a complete typed term, not a matcher reduction of
indexedEdgeMap against the different written decoder-family view. -/
private theorem selected_RX_diagonal (S : OddScale)
    (word : (CF S).Cochain2 (2 : StepIndex 4).castSucc)
    (z : (state S 2).presentation.Z) (b : Fin 2) :
    ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 word
      ((A S).induced.zPairEquiv (z,b)).val = word z := by
  have hm : ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 word =
      ((indexedDecoderData S 4).rxMap (2 : StepIndex 4)).map2 word :=
    congrArg (fun m : BDL26CochainMap (CF S) (2 : StepIndex 4) => m.map2 word)
      (selected_RX_eq S)
  exact (congrArg (fun w : Word3 S => w ((A S).induced.zPairEquiv (z,b)).val) hm).trans
    ((A S).induced.map2_diagonal word z b)

/-- A genuine syndrome with only retained-Z coordinates must be diagonal.
This uses the proved, unrestricted canonical assembly theorem, not the disputed
component-locality or witness-foot lemma. -/
theorem zero_aux_valid_diagonal (S : OddScale) (sigma : Word3 S)
    (hvalid : sigma ∈ LinearMap.range (d3 S))
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q) sigma = 0)
    (z : (state S 2).presentation.Z) :
    sigma ((A S).induced.zPairEquiv (z,0)).val =
      sigma ((A S).induced.zPairEquiv (z,1)).val := by
  have hcx := actual_cx_total_boundary_zero S sigma hx
  have hafter : rxSigmaAfterCx (A S) sigma = sigma := by
    change sigma + d3 S (cxCorrectionTotal (A S) sigma) = sigma
    rw [hcx,add_zero]
  have hcq := actual_cq_total_boundary_zero S sigma (by simpa only [hafter] using hq)
  have hc : d3 S (rxCorrectionTotal (A S) sigma) = 0 := by
    rw [rxCorrectionTotal, map_add, hcx, hcq, add_zero]
  let s : (indexedFamily S 4).Syndrome (2 : StepIndex 4).succ := ⟨sigma,hvalid⟩
  let lower := (rxStepOutput S 4 (2 : StepIndex 4) (by decide) s).coarse.val
  have hcorr : (rxStepOutput S 4 (2 : StepIndex 4) (by decide) s).correction =
      rxCorrectionTotal (A S) sigma :=
    rxStepOutput_correction S 4 (2 : StepIndex 4) (by decide) s
  have hd : d3 S (rxStepOutput S 4 (2 : StepIndex 4) (by decide) s).correction = 0 :=
    (congrArg (d3 S) hcorr).trans hc
  have hasm : sigma =
      ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 lower := by
    calc
      sigma = d3 S (rxStepOutput S 4 (2 : StepIndex 4) (by decide) s).correction +
          ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 lower :=
        rxStepOutput_relation S 4 (2 : StepIndex 4) (by decide) s
      _ = 0 + ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 lower :=
        congrArg (fun w : Word3 S =>
          w + ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 lower) hd
      _ = _ := zero_add _
  have hpair (b : Fin 2) : sigma ((A S).induced.zPairEquiv (z,b)).val = lower z :=
    (congrArg (fun w : Word3 S => w ((A S).induced.zPairEquiv (z,b)).val) hasm).trans
      (selected_RX_diagonal S lower z b)
  exact (hpair 0).trans (hpair 1).symm

/-- The directly checkable retained-copy obstruction used at the end. -/
theorem zero_aux_imbalance_not_boundary (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q) sigma = 0)
    (z : (state S 2).presentation.Z)
    (hneq : sigma ((A S).induced.zPairEquiv (z,0)).val ≠
      sigma ((A S).induced.zPairEquiv (z,1)).val) :
    sigma ∉ LinearMap.range (d3 S) := by
  intro hvalid
  exact hneq (zero_aux_valid_diagonal S sigma hvalid hx hq z)

abbrev LocalQWord (S : OddScale) (q : (state S 2).presentation.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ S).correctionRegion q))
abbrev LocalQSyndrome (S : OddScale) (q : (state S 2).presentation.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ S).syndromeRegion q))

noncomputable def terminalVertex (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true)
    (b : Fin 2) : LocalRegionIndex ((LQ S).correctionRegion q) :=
  rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q
    (b, Sum.inl (Sum.inr ⟨z,hqz⟩))

theorem terminalVertex_ne (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    terminalVertex S q z hqz 0 ≠ terminalVertex S q z hqz 1 := by
  intro he
  have hc := (rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q).injective he
  have hb := congrArg Prod.fst hc
  exact (by decide : (0 : Fin 2) ≠ 1) hb

noncomputable def terminalIndicator (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    LocalQWord S q :=
  fun v => if v = terminalVertex S q z hqz 0 then 1 else 0

noncomputable def terminalSyndrome (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    LocalQSyndrome S q :=
  (A S).contract.rx_local_complexes.cqDelta1 q (terminalIndicator S q z hqz)

/-- Both terminals exist at every OddScale; no half_pos is involved. -/
theorem terminalSyndrome_ne_zero (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    terminalSyndrome S q z hqz ≠ 0 := by
  intro hz
  have h0 := rxQ_kernel_constant S 4 (2 : StepIndex 4) (by decide) q
    (terminalIndicator S q z hqz) hz (0, Sum.inl (Sum.inr ⟨z,hqz⟩))
  have h1 := rxQ_kernel_constant S 4 (2 : StepIndex 4) (by decide) q
    (terminalIndicator S q z hqz) hz (1, Sum.inl (Sum.inr ⟨z,hqz⟩))
  have hbad := h0.trans h1.symm
  have hne := terminalVertex_ne S q z hqz
  change terminalIndicator S q z hqz (terminalVertex S q z hqz 0) =
    terminalIndicator S q z hqz (terminalVertex S q z hqz 1) at hbad
  have hv : (1 : BDL26Field) = 0 := by
    simpa [terminalIndicator,hne.symm] using hbad
  exact one_ne_zero hv

/-- The exact same existential predicate as the actual cqWitnessAt.
This is a name for the real choice, not a replacement minimizer. -/
noncomputable def actualQSection (S : OddScale) (q : (state S 2).presentation.Q)
    (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    LocalQWord S q :=
  Classical.choose ((A S).contract.local_boundary_weight_budgets.cq q t ht)

theorem actualQSection_spec (S : OddScale) (q : (state S 2).presentation.Q)
    (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    (A S).contract.rx_local_complexes.cqDelta1 q (actualQSection S q t ht) = t ∧
      HammingWeight ((A S).contract.support_decomposition.cqFlow q
        (actualQSection S q t ht)) ≤ HammingWeight t :=
  Classical.choose_spec ((A S).contract.local_boundary_weight_budgets.cq q t ht)

/-- Every genuine selected solution of the terminal query has the same
copy imbalance. It may be the indicator or its complement. -/
theorem terminal_solution_imbalance (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true)
    (w : LocalQWord S q)
    (hw : (A S).contract.rx_local_complexes.cqDelta1 q w =
      terminalSyndrome S q z hqz) :
    w (terminalVertex S q z hqz 0) + w (terminalVertex S q z hqz 1) = 1 := by
  let g := terminalIndicator S q z hqz
  have hk : (A S).contract.rx_local_complexes.cqDelta1 q (w+g) = 0 := by
    rw [map_add, hw]
    exact ZModModule.add_self _
  have h0 := rxQ_kernel_constant S 4 (2 : StepIndex 4) (by decide) q (w+g) hk
    (0, Sum.inl (Sum.inr ⟨z,hqz⟩))
  have h1 := rxQ_kernel_constant S 4 (2 : StepIndex 4) (by decide) q (w+g) hk
    (1, Sum.inl (Sum.inr ⟨z,hqz⟩))
  have hne := terminalVertex_ne S q z hqz
  have hboth : (w+g) (terminalVertex S q z hqz 0) =
      (w+g) (terminalVertex S q z hqz 1) := h0.trans h1.symm
  have he : w (terminalVertex S q z hqz 0) + 1 =
      w (terminalVertex S q z hqz 1) := by
    simpa [Pi.add_apply,g,terminalIndicator,hne.symm] using hboth
  rw [← he, ← add_assoc, ZModModule.add_self, zero_add]

/-- Zero-query section values need not vanish, but their global boundary does. -/
theorem actualQSection_zero_boundary (S : OddScale) (q : (state S 2).presentation.Q)
    (ht : (0 : LocalQSyndrome S q) ∈
      LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q)
      (actualQSection S q 0 ht)) = 0 := by
  let w := actualQSection S q 0 ht
  have hs := actualQSection_spec S q 0 ht
  have hf : (A S).contract.support_decomposition.cqFlow q w = 0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    apply Nat.eq_zero_of_le_zero
    simpa only [HammingWeight_zero] using hs.2
  have hdec := (A S).contract.support_decomposition.cqDelta1_decomposition q w
  rw [hs.1,hf,map_zero,zero_add] at hdec
  exact hdec

/-- Equal literal cleaned queries select the same real Classical.choose value.
The private cqWitnessAt is unfolded definitionally; no uniqueness of solutions
is assumed. -/
theorem actual_cq_reselect (S : OddScale) (sigma : Word3 S)
    (q : (state S 2).presentation.Q) (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q))
    (hquery : restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = t) :
    cqComponentTotal (A S) sigma q =
      extendWordLinear ((LQ S).correctionRegion q) (actualQSection S q t ht) := by
  classical
  have hr : CqLocalRangeAt (A S) sigma q := by
    change restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) ∈ _
    rw [hquery]
    exact ht
  unfold cqComponentTotal
  rw [dif_pos hr]
  change extendWordLinear ((LQ S).correctionRegion q)
    (Classical.choose ((A S).contract.local_boundary_weight_budgets.cq q
      (restrictWordLinear ((LQ S).syndromeRegion q)
        (rxSigmaAfterCx (A S) sigma)) hr)) = _
  congr 1
  let Pquery : LocalQWord S q → Prop := fun f =>
    (A S).contract.rx_local_complexes.cqDelta1 q f =
      restrictWordLinear ((LQ S).syndromeRegion q) (rxSigmaAfterCx (A S) sigma) ∧
    HammingWeight ((A S).contract.support_decomposition.cqFlow q f) ≤
      HammingWeight (restrictWordLinear ((LQ S).syndromeRegion q)
        (rxSigmaAfterCx (A S) sigma))
  let Pt : LocalQWord S q → Prop := fun f =>
    (A S).contract.rx_local_complexes.cqDelta1 q f = t ∧
    HammingWeight ((A S).contract.support_decomposition.cqFlow q f) ≤ HammingWeight t
  have hp : Pquery = Pt := by
    funext f
    dsimp only [Pquery, Pt]
    rw [hquery]
  have hchoose : ∀ (eqry : ∃ f, Pquery f) (et : ∃ f, Pt f),
      @Classical.choose _ Pquery eqry = @Classical.choose _ Pt et := by
    rw [hp]
    intro eqry et
    rfl
  exact hchoose
    ((A S).contract.local_boundary_weight_budgets.cq q
      (restrictWordLinear ((LQ S).syndromeRegion q) (rxSigmaAfterCx (A S) sigma)) hr)
    ((A S).contract.local_boundary_weight_budgets.cq q t ht)

open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps

abbrev seedQ (S : OddScale) : FamilyQ S 4 (0 : LevelIndex 4) := baseFaceQ 0 0
abbrev seedZ (S : OddScale) : FamilyZ S 4 (0 : LevelIndex 4) := baseFaceZ 0
noncomputable def seedError (S : OddScale) :
    (CF S).Correction (0 : LevelIndex 4) :=
  fun q => if q = seedQ S then 1 else 0
noncomputable def nu0 (S : OddScale) :
    (CF S).Syndrome (0 : LevelIndex 4) :=
  ⟨(CF S).coboundary1 0 (seedError S), ⟨seedError S,rfl⟩⟩
noncomputable def nu1 (S : OddScale) :
    (CF S).Syndrome (1 : LevelIndex 4) :=
  ((indexedDecoderData S 4).selectedMap (0 : StepIndex 4)).mapSyndrome (nu0 S)
noncomputable def gamma2 (S : OddScale) :
    (BDL26CanonicalHistoryMarks.Data S 2).family.Syndrome (0 : LevelIndex 2) :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 4 (1 : StepIndex 4) (nu1 S)

noncomputable def baseRetainedZ (S : OddScale) : FamilyZ S 4 (1 : LevelIndex 4) :=
  (rxData S 4 (0 : StepIndex 4) (by decide)).induced.zPairEquiv (seedZ S,0) |>.val
noncomputable def r2 (S : OddScale) : FamilyZ S 4 (2 : LevelIndex 4) :=
  ⟨baseRetainedZ S,
    rzMap1ZRoot (state S 1).presentation (state S 1).admissible (baseRetainedZ S) S⟩
noncomputable def E2 (S : OddScale) := actualBaseDecode S 2 (gamma2 S)

/-- These are auxiliary defining words only; they do not add history below C2. -/
theorem nu0_at_seed (S : OddScale) : (nu0 S).val (seedZ S) = 1 := by
  classical
  have hi : (state S 0).presentation.qz (seedQ S) (seedZ S) = true :=
    baseTannerSquarePresentation.data.faceQ_qz (0 : BaseFace) 0
  change (CF S).coboundary1 0 (seedError S) (seedZ S) = 1
  rw [CF_coboundary1]
  change (∑ q : FamilyQ S 4 (0 : LevelIndex 4),
    seedError S q * if (state S 0).presentation.qz q (seedZ S) = true then 1 else 0) = 1
  have hs := sum_single_value
    (fun q : FamilyQ S 4 (0 : LevelIndex 4) =>
      seedError S q * if (state S 0).presentation.qz q (seedZ S) = true then 1 else 0)
    (seedQ S) (by intro q hq; simp [seedError,hq])
  exact hs.trans (by simp [seedError,hi])

theorem nu1_at_retained (S : OddScale) : (nu1 S).val (baseRetainedZ S) = 1 := by
  change ((indexedDecoderData S 4).selectedMap (0 : StepIndex 4)).map2
    (nu0 S).val ((rxData S 4 0 (by decide)).induced.zPairEquiv (seedZ S,0)).val = 1
  rw [selectedMap_eq]
  exact ((rxData S 4 (0 : StepIndex 4) (by decide)).induced.map2_diagonal
    (nu0 S).val (seedZ S) 0).trans (nu0_at_seed S)

theorem gamma2_at_r2 (S : OddScale) : (gamma2 S).val (r2 S) = 1 := by
  change BDL26RZMap1CoordinateBridge.map2Coord (state S 1).presentation
    (state S 1).admissible S (nu1 S).val
      ⟨baseRetainedZ S,rzMap1ZRoot (state S 1).presentation
        (state S 1).admissible (baseRetainedZ S) S⟩ = 1
  rw [BDL26OwnerParentObstruction.rzMap2_apply]
  simpa using nu1_at_retained S

theorem gamma2_nonzero (S : OddScale) : (gamma2 S).val ≠ 0 := by
  intro he
  have h := gamma2_at_r2 S
  rw [he] at h
  exact zero_ne_one h

/-- A real nonzero base syndrome supplies a real adjacent correction coordinate. -/
theorem actual_base_neighbor_exists (S : OddScale) :
    ∃ q : (state S 2).presentation.Q,
      (state S 2).presentation.qz q (r2 S) = true ∧ E2 S q ≠ 0 := by
  classical
  have hb : (CF S).coboundary1 (2 : LevelIndex 4) (E2 S) = (gamma2 S).val :=
    actualBaseDecode_rightInverse S 2 (gamma2 S)
  have he := congrFun hb (r2 S)
  rw [CF_coboundary1,gamma2_at_r2] at he
  change (∑ q : (state S 2).presentation.Q,
    E2 S q * if (state S 2).presentation.qz q (r2 S) = true then 1 else 0) = 1 at he
  by_contra hn
  push Not at hn
  have hz : (∑ q : (state S 2).presentation.Q,
      E2 S q * if (state S 2).presentation.qz q (r2 S) = true then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : (state S 2).presentation.qz q (r2 S) = true
    · simp only [if_pos hq, hn q hq, zero_mul]
    · simp only [if_neg hq, mul_zero]
  exact zero_ne_one (hz.symm.trans he)

noncomputable def q2 (S : OddScale) : (state S 2).presentation.Q :=
  Classical.choose (actual_base_neighbor_exists S)
theorem q2_incidence (S : OddScale) : (state S 2).presentation.qz (q2 S) (r2 S) = true :=
  (Classical.choose_spec (actual_base_neighbor_exists S)).1

noncomputable def localSeed (S : OddScale) (q : (state S 2).presentation.Q) :
    LocalQWord S q :=
  if h : q2 S = q then h ▸ terminalIndicator S (q2 S) (r2 S) (q2_incidence S) else 0
noncomputable def localQuery (S : OddScale) (q : (state S 2).presentation.Q) :
    LocalQSyndrome S q := (A S).contract.rx_local_complexes.cqDelta1 q (localSeed S q)
theorem localQuery_range (S : OddScale) (q : (state S 2).presentation.Q) :
    localQuery S q ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q) :=
  ⟨localSeed S q,rfl⟩
noncomputable def localW (S : OddScale) (q : (state S 2).presentation.Q) : LocalQWord S q :=
  actualQSection S q (localQuery S q) (localQuery_range S q)
noncomputable def G (S : OddScale) : Correction3 S :=
  ∑ q, extendWordLinear ((LQ S).correctionRegion q) (localW S q)

theorem localSeed_at_q2 (S : OddScale) :
    localSeed S (q2 S) = terminalIndicator S (q2 S) (r2 S) (q2_incidence S) := by
  simp [localSeed]

theorem localW_at_q2_imbalance (S : OddScale) :
    localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 0) +
      localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 1) = 1 := by
  apply terminal_solution_imbalance
  exact (actualQSection_spec S (q2 S) (localQuery S (q2 S))
    (localQuery_range S (q2 S))).1.trans (by
      rw [localQuery, localSeed_at_q2]
      rfl)

theorem other_localW_boundary_zero (S : OddScale) (q : (state S 2).presentation.Q)
    (hq : q ≠ q2 S) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q)) = 0 := by
  have ht : localQuery S q = 0 := by
    simp only [localQuery, localSeed, dif_neg hq.symm, map_zero]
  have hs : (A S).contract.rx_local_complexes.cqDelta1 q (localW S q) = localQuery S q ∧
      HammingWeight ((A S).contract.support_decomposition.cqFlow q (localW S q)) ≤
        HammingWeight (localQuery S q) :=
    actualQSection_spec S q (localQuery S q) (localQuery_range S q)
  have hd : (A S).contract.rx_local_complexes.cqDelta1 q (localW S q) = 0 := hs.1.trans ht
  have hf : (A S).contract.support_decomposition.cqFlow q (localW S q) = 0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    apply Nat.eq_zero_of_le_zero
    calc
      HammingWeight ((A S).contract.support_decomposition.cqFlow q (localW S q)) ≤
          HammingWeight (localQuery S q) := hs.2
      _ = 0 := by rw [ht,HammingWeight_zero]
  have hdec := (A S).contract.support_decomposition.cqDelta1_decomposition q (localW S q)
  rw [hd,hf,map_zero,zero_add] at hdec
  exact hdec

/-- The assembled Q choice has no coordinate in any actual X correction fibre. -/
theorem G_restrict_X (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).correctionRegion x) (G S) = 0 := by
  classical
  ext p
  change (∑ q, extendWordLinear ((LQ S).correctionRegion q) (localW S q)) p.val = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hnot : p.val ∉ (LQ S).correctionRegion q := by
    intro hq
    have hxU : p.val ∈ correctionRegionUnion (LX S) :=
      Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, p.property⟩
    have hqU : p.val ∈ (A S).qCorrectionSector := by
      rw [(A S).qCorrectionSector_eq_regions]
      exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, hq⟩
    exact (Finset.disjoint_left.mp (A S).correction_sectors_disjoint) hxU hqU
  change (if h : p.val ∈ (LQ S).correctionRegion q then _ else 0) = 0
  rw [dif_neg hnot]

/-- Pairwise-disjoint actual Q fibres recover their own chosen word. -/
theorem G_restrict_Q (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).correctionRegion q) (G S) = localW S q := by
  classical
  ext p
  change (∑ r, extendWordLinear ((LQ S).correctionRegion r) (localW S r)) p.val = _
  rw [Finset.sum_apply]
  have hz (other : (state S 2).presentation.Q) (hne : other ≠ q) :
      extendWordLinear ((LQ S).correctionRegion other) (localW S other) p.val = 0 := by
    have hnot : p.val ∉ (LQ S).correctionRegion other := by
      intro ho
      exact (Finset.disjoint_left.mp
        ((A S).cq_correction_regions_pairwise_disjoint q other hne.symm)) p.property ho
    exact dif_neg hnot
  have hs := sum_single_value
    (fun r : (state S 2).presentation.Q =>
      extendWordLinear ((LQ S).correctionRegion r) (localW S r) p.val) q hz
  exact hs.trans (by exact dif_pos p.property)

noncomputable def lower3 (S : OddScale) :
    (CF S).Syndrome level3 := by
  let lifted : (CF S).Syndrome level3 :=
    ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).mapSyndrome (gamma2 S)
  refine ⟨lifted.val + d3 S (G S), ?_⟩
  obtain ⟨e,he⟩ := lifted.property
  exact ⟨e+G S, by rw [map_add,he]⟩

theorem lower3_val (S : OddScale) : (lower3 S).val =
    ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val + d3 S (G S) := rfl

private theorem map2_X_query_zero (S : OddScale)
    (b : (CF S).Cochain2 (2 : LevelIndex 4))
    (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x)
      (((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b) = 0 := by
  ext p
  have hx : p.val ∈ (A S).xSector := by
    rw [(A S).xSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ x,p.property⟩
  have hz : p.val ∉ (A S).induced.zSector := by
    intro hp
    have hp' : p.val ∈ (A S).zSector := by
      rw [(A S).zSector_eq_induced]
      exact hp
    exact (Finset.disjoint_left.mp (A S).sectors_pairwise_disjoint.2.1) hx hp'
  change ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b p.val = 0
  rw [selectedMap_eq]
  exact (A S).induced.map2_auxiliary_zero b p.val hz

private theorem map2_Q_query_zero (S : OddScale)
    (b : (CF S).Cochain2 (2 : LevelIndex 4))
    (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q)
      (((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b) = 0 := by
  ext p
  have hq : p.val ∈ (A S).qSector := by
    rw [(A S).qSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ q,p.property⟩
  have hz : p.val ∉ (A S).induced.zSector := by
    intro hp
    have hp' : p.val ∈ (A S).zSector := by
      rw [(A S).zSector_eq_induced]
      exact hp
    exact (Finset.disjoint_left.mp (A S).sectors_pairwise_disjoint.2.2) hq hp'
  change ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b p.val = 0
  rw [selectedMap_eq]
  exact (A S).induced.map2_auxiliary_zero b p.val hz

theorem lower3_X_query_zero (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) (lower3 S).val = 0 := by
  rw [lower3_val, map_add, map2_X_query_zero, zero_add]
  rw [(A S).contract.support_decomposition.cxDelta1_restriction_global,
    G_restrict_X, map_zero]

theorem lower3_Q_query (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) (lower3 S).val = localQuery S q := by
  rw [lower3_val, map_add, map2_Q_query_zero, zero_add]
  rw [(A S).contract.support_decomposition.cqDelta1_restriction_global q (G S)
    (G_restrict_X S), G_restrict_Q]
  exact (actualQSection_spec S q (localQuery S q) (localQuery_range S q)).1

theorem lower3_after_X (S : OddScale) :
    rxSigmaAfterCx (A S) (lower3 S).val = (lower3 S).val := by
  have h := actual_cx_total_boundary_zero S (lower3 S).val (lower3_X_query_zero S)
  change (lower3 S).val + d3 S (cxCorrectionTotal (A S) (lower3 S).val) = (lower3 S).val
  rw [h,add_zero]

theorem lower3_actual_Q_total (S : OddScale) :
    cqCorrectionTotal (A S) (lower3 S).val = G S := by
  classical
  change (∑ q, cqComponentTotal (A S) (lower3 S).val q) = _
  apply Finset.sum_congr rfl
  intro q _
  exact actual_cq_reselect S (lower3 S).val q (localQuery S q) (localQuery_range S q)
    (by rw [lower3_after_X]; exact lower3_Q_query S q)

theorem lower3_after_Q (S : OddScale) :
    rxSigmaAfterCq (A S) (lower3 S).val =
      ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val := by
  rw [rxSigmaAfterCq,lower3_after_X,lower3_actual_Q_total,lower3_val,
    add_assoc,ZModModule.add_self,add_zero]

theorem lower3_actual_coarse (S : OddScale) :
    (rxStepOutput S 4 (2 : StepIndex 4) (by decide) (lower3 S)).coarse = gamma2 S := by
  apply Subtype.ext
  have hm : ((indexedDecoderData S 4).rxMap (2 : StepIndex 4)).map2 (gamma2 S).val =
      ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val :=
    (congrArg (fun m : BDL26CochainMap (CF S) (2 : StepIndex 4) => m.map2 (gamma2 S).val)
      (selected_RX_eq S)).symm
  have hp : coarseProjection (A S) (rxSigmaAfterCq (A S) (lower3 S).val) =
      (gamma2 S).val :=
    coarseProjection_eq_of_map2 (A S) _ (gamma2 S).val
      (hm.trans (lower3_after_Q S).symm)
  exact (rxStepOutput_coarse S 4 (2 : StepIndex 4) (by decide) (lower3 S)).trans hp

noncomputable def upper4 (S : OddScale) : BDL26CanonicalHistoryMarks.Input S 2 :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 4 (3 : StepIndex 4) (lower3 S)

open BDL26RXLocalReplacement BDL26RXStagedRestriction

/-- Only the actual transported flow projection is normalized in this identity. -/
theorem actual_Q_flow_raw_value (S : OddScale) (q : (state S 2).presentation.Q)
    (w : LocalQWord S q) (z : (state S 2).presentation.Z) (b : Fin 2) :
    (A S).contract.support_decomposition.cqFlow q w
        ((A S).induced.zPairEquiv (z,b)).val =
      qFlow (state S 2).presentation S q
        (fun v => w (rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q v))
        (Sum.inr (z,b)) := by
  rfl

/-- Literal terminal evaluation in the actual physical Q chart. -/
theorem q_boundary_at_terminal (S : OddScale) (q : (state S 2).presentation.Q)
    (w : LocalQWord S q) (z : (state S 2).presentation.Z)
    (hqz : (state S 2).presentation.qz q z = true) (b : Fin 2) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q) w)
      ((A S).induced.zPairEquiv (z,b)).val = w (terminalVertex S q z hqz b) := by
  have hflow : d3 S (extendWordLinear ((LQ S).correctionRegion q) w)
      ((A S).induced.zPairEquiv (z,b)).val =
    (A S).contract.support_decomposition.cqFlow q w
      ((A S).induced.zPairEquiv (z,b)).val :=
    rxQ_boundary_z_flow S 4 (2 : StepIndex 4) (by decide) q w z b
  calc
    _ = (A S).contract.support_decomposition.cqFlow q w
        ((A S).induced.zPairEquiv (z,b)).val := hflow
    _ = qFlow (state S 2).presentation S q
        (fun v => w (rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q v))
        (Sum.inr (z,b)) := actual_Q_flow_raw_value S q w z b
    _ = _ := by
      rw [qFlow_at_z]
      simp only [rxQOutgoing,dif_pos hqz,rxQZDegreeOne,wordPullback_apply,terminalVertex]

theorem G_boundary_at_retained (S : OddScale) (b : Fin 2) :
    d3 S (G S) ((A S).induced.zPairEquiv (r2 S,b)).val =
      localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) := by
  classical
  rw [G,map_sum,Finset.sum_apply]
  have hz (q : (state S 2).presentation.Q) (hq : q ≠ q2 S) :
      d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q))
        ((A S).induced.zPairEquiv (r2 S,b)).val = 0 :=
    congrFun (other_localW_boundary_zero S q hq) _
  have hs := sum_single_value
    (fun q : (state S 2).presentation.Q =>
      d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q))
        ((A S).induced.zPairEquiv (r2 S,b)).val) (q2 S) hz
  exact hs.trans (q_boundary_at_terminal S (q2 S) (localW S (q2 S))
    (r2 S) (q2_incidence S) b)

theorem lower3_retained_value (S : OddScale) (b : Fin 2) :
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val =
      1 + localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) := by
  calc
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val =
        ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val
            ((A S).induced.zPairEquiv (r2 S,b)).val +
          d3 S (G S) ((A S).induced.zPairEquiv (r2 S,b)).val :=
      congrArg (fun w : Word3 S => w ((A S).induced.zPairEquiv (r2 S,b)).val) (lower3_val S)
    _ = (gamma2 S).val (r2 S) +
        localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) :=
      congrArg₂ (fun a c : BDL26Field => a+c)
        (selected_RX_diagonal S (gamma2 S).val (r2 S) b) (G_boundary_at_retained S b)
    _ = _ := congrArg (fun a : BDL26Field =>
      a + localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b))
        (gamma2_at_r2 S)

theorem lower3_retained_imbalance (S : OddScale) :
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,0)).val +
      (lower3 S).val ((A S).induced.zPairEquiv (r2 S,1)).val = 1 := by
  rw [lower3_retained_value,lower3_retained_value]
  calc
    (1 + _) + (1 + _) = ((1 : BDL26Field)+1) +
        (localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 0) +
          localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 1)) := by abel
    _ = 1 := by rw [ZModModule.add_self,localW_at_q2_imbalance,zero_add]

theorem lower3_retained_nonzero (S : OddScale) :
    ∃ b : Fin 2, (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val ≠ 0 := by
  have hi := lower3_retained_imbalance S
  by_cases h0 : (lower3 S).val ((A S).induced.zPairEquiv (r2 S,0)).val = 0
  · refine ⟨1,?_⟩
    intro h1
    rw [h0,h1,zero_add] at hi
    exact zero_ne_one hi
  · exact ⟨0,h0⟩

/-- The selected RZ map reflects the actual coboundary range, on arbitrary words. -/
theorem top_RZ_reflects_boundary (S : OddScale) (eta : Word3 S)
    (h : ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 eta ∈
      LinearMap.range ((CF S).coboundary1 level4)) :
    eta ∈ LinearMap.range (d3 S) := by
  obtain ⟨e,he⟩ := h
  let Z := rzData S 4 (3 : StepIndex 4) (by decide)
  refine ⟨Z.induced.correctionProjection e,?_⟩
  have hc := rzData_inducedCoboundaryCompatibility S 4 (3 : StepIndex 4) (by decide) e
  change RZCoarseGraining.RZCoarseGrainingData.topParity Z
    (((CF S).coboundary1 level4) e) =
      d3 S (Z.induced.correctionProjection e) at hc
  rw [he] at hc
  have hm : RZCoarseGraining.RZCoarseGrainingData.topParity Z
      (((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 eta) = eta := by
    rw [selectedMap_eq]
    exact RZCoarseGraining.topParity_rzMap_map2 Z eta
  exact hc.symm.trans hm

noncomputable def topWitness (S : OddScale) (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    (CF S).Cochain2 level4 :=
  maskWord (Finset.univ.filter (fun p =>
    actualTopNode S
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) p) ∈
        BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)) sigma.val

/-- Pointwise unfolding keeps the full actual root predicate abstract in the
finite-word transport. No equation matcher has to identify a closed family. -/
private theorem topWitness_apply (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) (p : FamilyZ S 4 level4) :
    topWitness S sigma p =
      if actualTopNode S
        (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) p) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 sigma then sigma.val p else 0 :=
  mask_filter_apply _ sigma.val p

noncomputable def topOut (S : OddScale) := actualStep S 4 (3 : StepIndex 4) (upper4 S)
noncomputable def nextOut (S : OddScale) := actualStep S 4 (2 : StepIndex 4) (topOut S).coarse
noncomputable def storedBase (S : OddScale) :
    RecursiveBaseLevelCorrection (LevelTwoHistory.suffixData (indexedDecoderData S 4)) where
  input := (nextOut S).coarse
  correction := (actualBase S 2).decode (nextOut S).coarse
  relation := ((actualBase S 2).rightInverse (nextOut S).coarse).symm

theorem topOut_coarse (S : OddScale) : (topOut S).coarse = lower3 S := by
  change (actualStep S 4 (3 : StepIndex 4) (upper4 S)).coarse = _
  rw [actualStep_rz S 4 3 (by decide)]
  exact rzStepOutput_map2_coarse S 4 3 (by decide) (lower3 S)

theorem nextOut_coarse (S : OddScale) : (nextOut S).coarse = gamma2 S := by
  change (actualStep S 4 (2 : StepIndex 4) (topOut S).coarse).coarse = _
  rw [topOut_coarse,actualStep_rx S 4 2 (by decide)]
  exact lower3_actual_coarse S

/-- Exactly the two physical steps and the actual C2 correction; no lower step. -/
theorem actual_history_exact (S : OddScale) : actualHistory S 2 (upper4 S) =
    [CorrectionHistoryEntry.step (1 : StepIndex 2)
       (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 1 (topOut S)),
     CorrectionHistoryEntry.step (0 : StepIndex 2)
       (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 0 (nextOut S)),
     CorrectionHistoryEntry.base (storedBase S)] := by
  exact LevelTwoHistory.stoppedHistory_two (indexedDecoderData S 4)
    (actualAboveTwoSteps S 2) (actualBase S 2) (upper4 S)

theorem actual_mid_input (S : OddScale) :
    BDL26CanonicalHistoryMarks.inputAt S 2 (upper4 S) (1 : LevelIndex 2) = lower3 S := by
  have hm : CorrectionHistoryEntry.step (0 : StepIndex 2)
      (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 0 (nextOut S)) ∈
        actualHistory S 2 (upper4 S) := by
    rw [actual_history_exact]
    simp
  have hi := BDL26CanonicalHistoryMarks.inputAt_step S 2 (upper4 S) (0 : StepIndex 2)
    (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 0 (nextOut S)) hm
  change BDL26CanonicalHistoryMarks.inputAt S 2 (upper4 S) (1 : LevelIndex 2) =
    (nextOut S).input at hi
  have hin : (nextOut S).input = (topOut S).coarse :=
    (actualStep_relation S 4 (2 : StepIndex 4)).input_eq (topOut S).coarse
  exact hi.trans (hin.trans (topOut_coarse S))

theorem actual_base_input (S : OddScale) :
    BDL26CanonicalHistoryMarks.baseInput S 2 (upper4 S) = gamma2 S := by
  have hm : CorrectionHistoryEntry.base (storedBase S) ∈ actualHistory S 2 (upper4 S) := by
    rw [actual_history_exact]
    simp
  have hi := BDL26CanonicalHistoryMarks.inputAt_base S 2 (upper4 S) (storedBase S) hm
  change BDL26CanonicalHistoryMarks.baseInput S 2 (upper4 S) = (nextOut S).coarse at hi
  exact hi.trans (nextOut_coarse S)

/-- The true mark definitions add only Z-type vertices at physical top C4. -/
theorem actual_top_marks_are_Z (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    ∀ v : GraphVertex S 4,
      actualTopNode S v ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma → ∃ z, v = zVertex S 3 z := by
  intro v hv
  have hv' : BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) v ∈
      BDL26CanonicalHistoryMarks.marks S 2 sigma :=
    Eq.mp (congrArg (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
      w ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma) (actualTopNode_physical S v)) hv
  have hm := (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 sigma
    (2 : LevelIndex 2) v).mp hv'
  change v ∈ BDL26CanonicalHistoryMarks.aboveMarks S 2 sigma (1 : StepIndex 2) at hm
  rcases (BDL26CanonicalHistoryMarks.mem_aboveMarks S 2 sigma (1 : StepIndex 2) v).mp hm with
    ⟨p,ho,_⟩ | ⟨a,ho,_⟩ | ⟨a,p,ho,_⟩
  · change zVertex S 3 p.1 = v at ho
    exact ⟨p.1,ho.symm⟩
  · change zVertex S 3 _ = v at ho
    exact ⟨_,ho.symm⟩
  · change zVertex S 3 p.1 = v at ho
    exact ⟨p.1,ho.symm⟩

/-- The compiled generic isolation lemma on the same typed literal Sigma nodes.
No concrete graph record or recursive presentation is unfolded here. -/
theorem no_actual_top_Z_marked_neighbor (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (hparent : parent S 3 (zVertex S 3 z) = none)
    (w : BDL26CanonicalHistoryMarks.Node S 2)
    (hw : w ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma) :
    ¬ (decodingGraph S 4).adjacent (actualTopNode S (zVertex S 3 z)) w := by
  have hm : BDL26UniformTopOwnerIsolation.TopMarksAreZ S 3
      (BDL26CanonicalHistoryMarks.marks S 2 sigma) := by
    intro v hv
    obtain ⟨z,hz⟩ := actual_top_marks_are_Z S sigma v hv
    exact ⟨z,hz.trans (zVertex_eq S 3 z)⟩
  exact BDL26UniformTopOwnerIsolation.no_marked_neighbor S 3
    (BDL26CanonicalHistoryMarks.marks S 2 sigma) hm z hparent w hw

/-- The WHOLE canonical-root exclusion argument, including membership
elimination and its marked relation, is proved with arbitrary n and node u. -/
private theorem canonical_not_root (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u : BDL26CanonicalHistoryMarks.Node S n)
    (hne : u ≠ BDL26CanonicalHistoryMarks.root S n)
    (hout : ∀ w, BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u w → False) :
    u ∉ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  intro hk
  obtain ⟨_,_,hpath⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma u).mp hk
  exact no_path_of_no_outgoing (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma)
    u (BDL26CanonicalHistoryMarks.root S n) hne hout hpath

/-- No arbitrary lower marking is introduced: this uses the real rootComponent. -/
theorem actual_unparented_top_not_root (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (hp : parent S 3 (zVertex S 3 z) = none) :
    actualTopNode S (zVertex S 3 z) ∉
      BDL26CanonicalHistoryMarks.rootComponent S 2 sigma := by
  have hne : actualTopNode S (zVertex S 3 z) ≠
      BDL26CanonicalHistoryMarks.root S 2 := by
    intro heq
    have hl := congrArg (fun w : BDL26CanonicalHistoryMarks.Node S 2 => w.1.val) heq
    change 4 = 0 at hl
    omega
  exact canonical_not_root S 2 sigma (actualTopNode S (zVertex S 3 z)) hne
    (fun w hedge => no_actual_top_Z_marked_neighbor S sigma z hp w
      ((BDL26CanonicalHistoryMarks.markedAdjacent_iff S 2 sigma _ _).mp hedge).2.2
      ((BDL26CanonicalHistoryMarks.markedAdjacent_iff S 2 sigma _ _).mp hedge).1)

noncomputable def eta (S : OddScale) : Word3 S :=
  selectedWord (fun z : FamilyZ S 4 level3 => actualTopNode S (zVertex S 3 z) ∈
    BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)) (lower3 S).val

/-- Exact original literal coordinate formula, with its actual root unchanged. -/
private theorem eta_apply (S : OddScale) (z : FamilyZ S 4 level3) :
    eta S z = if actualTopNode S (zVertex S 3 z) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S) then (lower3 S).val z else 0 :=
  selectedWord_apply _ _ z

/-- Literal RX syndrome coordinates, typed on the actual upper carrier. -/
abbrev xFace3 (S : OddScale) (x : (state S 2).presentation.X)
    (f : DoubleCylinderFace (state S 2).presentation x S) : FamilyZ S 4 level3 :=
  Sum.inl (Sum.inl ⟨x,f⟩)
abbrev qEdge3 (S : OddScale) (q : (state S 2).presentation.Q)
    (e : QDoubleCylinderEdge (state S 2).presentation q S) : FamilyZ S 4 level3 :=
  Sum.inl (Sum.inr ⟨q,e⟩)

/-- These equalities normalize only one actual topCenter projection each. -/
theorem center_xFace3 (S : OddScale) (x : (state S 2).presentation.X)
    (f : DoubleCylinderFace (state S 2).presentation x S) :
    (A S).topCenter (xFace3 S x f) = Sum.inl x := by rfl
theorem center_qEdge3 (S : OddScale) (q : (state S 2).presentation.Q)
    (e : QDoubleCylinderEdge (state S 2).presentation q S) :
    (A S).topCenter (qEdge3 S q e) = Sum.inr (Sum.inl q) := by rfl

/-- Complete actual RX coordinate classification; no model partition changes. -/
theorem word3_coordinate_cases (S : OddScale) (p : FamilyZ S 4 level3) :
    (∃ x f, p = xFace3 S x f) ∨ (∃ q e, p = qEdge3 S q e) ∨
      (∃ z b, p = ((A S).induced.zPairEquiv (z,b)).val) := by
  rcases p with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,b⟩
  · exact Or.inl ⟨x,f,rfl⟩
  · exact Or.inr (Or.inl ⟨q,e,rfl⟩)
  · exact Or.inr (Or.inr ⟨z,b,rfl⟩)

/-- Typed actual top RZ owner, isolated from root-mask simplification. -/
theorem top_owner_apply (S : OddScale) (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2)
      (⟨z,v⟩ : FamilyZ S 4 level4) = zVertex S 3 z := by rfl

theorem upper4_val (S : OddScale) : (upper4 S).val =
    ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (lower3 S).val := rfl

/-- The single actual top RZ coordinate chart, normalized before rewriting. -/
theorem selected_top_map2_apply (S : OddScale) (word : Word3 S)
    (z : (state S 3).presentation.Z) (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 word ⟨z,v⟩ =
      if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
      then word z else 0 := by
  change map2Coord (state S 3).presentation (state S 3).admissible S word ⟨z,v⟩ = _
  exact BDL26OwnerParentObstruction.rzMap2_apply _ _ _ _ _ _

/-- The actual top root mask selects whole RZ Z blocks, on the actual input. -/
theorem topWitness_factor (S : OddScale) : topWitness S (upper4 S) =
    ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (eta S) := by
  classical
  funext p
  rcases p with ⟨z,v⟩
  have hm := topWitness_apply S (upper4 S) (⟨z,v⟩ : FamilyZ S 4 level4)
  rw [top_owner_apply] at hm
  calc
    topWitness S (upper4 S) ⟨z,v⟩ =
        if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
        then (upper4 S).val ⟨z,v⟩ else 0 := hm
    _ = if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
        then ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2
          (lower3 S).val ⟨z,v⟩ else 0 :=
      congrArg (fun word : (CF S).Cochain2 level4 =>
        if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
        then word ⟨z,v⟩ else 0) (upper4_val S)
    _ = if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
        then (if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
          then (lower3 S).val z else 0) else 0 :=
      congrArg (fun a : BDL26Field =>
        if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S) then a else 0)
          (selected_top_map2_apply S (lower3 S).val z v)
    _ = if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
        then (if actualTopNode S (zVertex S 3 z) ∈
          BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
          then (lower3 S).val z else 0) else 0 :=
      conditional_swap _ _ _ _ _ _ ((lower3 S).val z)
    _ = if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
        then eta S z else 0 :=
      congrArg (fun a : BDL26Field =>
        if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S then a else 0)
          (eta_apply S z).symm
    _ = _ := (selected_top_map2_apply S (eta S) z v).symm

theorem eta_X_face_zero (S : OddScale) (x : (state S 2).presentation.X)
    (f : DoubleCylinderFace (state S 2).presentation x S) :
    eta S (xFace3 S x f) = 0 := by
  have hn := actual_unparented_top_not_root S (upper4 S) (xFace3 S x f) (by rfl)
  exact selectedWord_zero _ _ (xFace3 S x f) hn

theorem eta_Q_edge_zero (S : OddScale) (q : (state S 2).presentation.Q)
    (e : QDoubleCylinderEdge (state S 2).presentation q S) :
    eta S (qEdge3 S q e) = 0 := by
  have hn := actual_unparented_top_not_root S (upper4 S) (qEdge3 S q e) (by rfl)
  exact selectedWord_zero _ _ (qEdge3 S q e) hn

private theorem word3_X_query_zero_of_aux_zero (S : OddScale) (word : Word3 S)
    (hface : ∀ x f, word (xFace3 S x f) = 0)
    (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) word = 0 := by
  apply restriction_zero_of_values
  intro p hp
  have ho := ((A S).topCenter_x_iff x p).mp hp
  rcases word3_coordinate_cases S p with ⟨y,f,he⟩ | ⟨q,e,he⟩ | ⟨z,b,he⟩
  · exact (congrArg word he).trans (hface y f)
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inl q) = Sum.inl x :=
      (center_qEdge3 S q e).symm.trans (hc.symm.trans ho)
    cases hbad
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inr z) = Sum.inl x :=
      ((A S).topCenter_coarse_pair z b).symm.trans (hc.symm.trans ho)
    cases hbad

private theorem word3_Q_query_zero_of_aux_zero (S : OddScale) (word : Word3 S)
    (hedge : ∀ q e, word (qEdge3 S q e) = 0)
    (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) word = 0 := by
  apply restriction_zero_of_values
  intro p hp
  have ho := ((A S).topCenter_q_iff q p).mp hp
  rcases word3_coordinate_cases S p with ⟨x,f,he⟩ | ⟨r,e,he⟩ | ⟨z,b,he⟩
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inl x = Sum.inr (Sum.inl q) :=
      (center_xFace3 S x f).symm.trans (hc.symm.trans ho)
    cases hbad
  · exact (congrArg word he).trans (hedge r e)
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inr z) = Sum.inr (Sum.inl q) :=
      ((A S).topCenter_coarse_pair z b).symm.trans (hc.symm.trans ho)
    cases hbad

theorem eta_X_query_zero (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) (eta S) = 0 :=
  word3_X_query_zero_of_aux_zero S (eta S) (eta_X_face_zero S) x

theorem eta_Q_query_zero (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) (eta S) = 0 :=
  word3_Q_query_zero_of_aux_zero S (eta S) (eta_Q_edge_zero S) q

/-- One original marked edge extends the actual root component. All vertices
are parameters, so no concrete history record is recursively normalized. -/
private theorem canonical_root_extend (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (hu : u ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (he : (decodingGraph S (n+2)).adjacent u v)
    (hv : v ∈ BDL26CanonicalHistoryMarks.rootComponent S n sigma) :
    u ∈ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  obtain ⟨hr,hm,hpath⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma v).mp hv
  exact (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma u).mpr
    ⟨hr,hu,(Relation.ReflTransGen.single ⟨he,hu,hm⟩).trans hpath⟩

/-- Original adjacent-parent extension with both vertices and the physical
step abstract. No concrete level-four graph is unfolded in the caller. -/
private theorem canonical_parent_root_extend (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) (i : StepIndex (n+2))
    (u : GraphVertex S i.succ.val) (v : GraphVertex S i.castSucc.val)
    (hp : parent S i.val u = some v)
    (hu : (⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n) ∈
      BDL26CanonicalHistoryMarks.marks S n sigma)
    (hv : (⟨i.castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S n) ∈
      BDL26CanonicalHistoryMarks.rootComponent S n sigma) :
    (⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n) ∈
      BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  have he : (decodingGraph S (n+2)).adjacent
      (⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n) ⟨i.castSucc,v⟩ := by
    apply Or.inr
    apply Or.inr
    refine ⟨i,?_⟩
    simpa only [dif_pos rfl, dif_pos True.intro] using (parent_interLevel_iff S (n+2) i v u).mp hp
  exact canonical_root_extend S n sigma _ _ hu he hv

/-- The original syndrome-input marking guard, on arbitrary actual snapshots. -/
private theorem canonical_input_owner_marked (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) (i : StepIndex n)
    (p : FamilyZ S (n+2) (LevelTwoHistory.physicalStep i).succ)
    (hp : (BDL26CanonicalHistoryMarks.outputAt S n sigma i).input.val p ≠ 0) :
    BDL26CanonicalHistoryMarks.physicalNode S n i.succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S n i p) ∈
        BDL26CanonicalHistoryMarks.marks S n sigma :=
  (BDL26CanonicalHistoryMarks.mem_marks_physical S n sigma i.succ _).mpr
    ((BDL26CanonicalHistoryMarks.mem_aboveMarks S n sigma i _).mpr
      (Or.inl ⟨p,rfl,hp⟩))

/-- An original nonzero base syndrome coordinate and its literal parent give
exactly the existing bottom root path, without computing a base decoder. -/
private theorem canonical_base_owner_root (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (p : FamilyZ S (n+2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (v : GraphVertex S 2) (u : GraphVertex S 1)
    (ho : BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p = v)
    (hp : (BDL26CanonicalHistoryMarks.baseInput S n sigma).val p ≠ 0)
    (hparent : parent S 1 v = some u) :
    BDL26CanonicalHistoryMarks.physicalNode S n 0 v ∈
      BDL26CanonicalHistoryMarks.rootComponent S n sigma :=
  BDL26CanonicalHistoryMarks.parented_base_in_rootComponent S n sigma v
    ((BDL26CanonicalHistoryMarks.mem_baseMarks S n sigma v).mpr (Or.inl ⟨p,ho,hp⟩))
    u hparent

/-- Only the actual RZ base-owner projection is reduced here. -/
private theorem base_r2_owner (S : OddScale) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 2 (r2 S) =
      zVertex S 1 (baseRetainedZ S) := by
  change @Vertex.z (state S 1).presentation (baseRetainedZ S) =
    zVertex S 1 (baseRetainedZ S)
  exact (zVertex_eq S 1 (baseRetainedZ S)).symm

/-- The seed RX parent is checked before any actual history is instantiated. -/
private theorem base_retained_parent (S : OddScale) :
    parent S 1 (zVertex S 1 (baseRetainedZ S)) = some (zVertex S 0 (seedZ S)) := by
  change rxParent baseTannerSquarePresentation S
    (Vertex.z (Sum.inr (seedZ S,0))) = some (Vertex.z (seedZ S))
  rfl

/-- The genuine retained base mark is derived from the stored input snapshot
and the actual nonzero seed coordinate, before any root-path construction. -/
private theorem actual_base_retained_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    zVertex S 1 (baseRetainedZ S) ∈ BDL26CanonicalHistoryMarks.baseMarks S 2 sigma := by
  have hvalue : (gamma2 S).val (r2 S) ≠ 0 :=
    fun hz => one_ne_zero ((gamma2_at_r2 S).symm.trans hz)
  have heval : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) =
      (gamma2 S).val (r2 S) :=
    congrArg (fun word :
      (BDL26CanonicalHistoryMarks.Data S 2).family.Syndrome (0 : LevelIndex 2) =>
        word.val (r2 S)) hbase
  have hnonzero : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) ≠ 0 :=
    fun hz => hvalue (heval.symm.trans hz)
  exact (BDL26CanonicalHistoryMarks.mem_baseMarks S 2 sigma
    (zVertex S 1 (baseRetainedZ S))).mpr
      (Or.inl ⟨r2 S,base_r2_owner S,hnonzero⟩)

/-- Marked reachability on an arbitrary node type. No scale, level, indexed
family, syndrome or computed finite component enters the proof parameters. -/
private structure MarkedRootPath {N : Type} (M : N → Prop) (R : N → N → Prop)
    (root w : N) : Prop where
  root_marked : M root
  marked : M w
  path : Relation.ReflTransGen R w root

/-- The original marked-root relation presented inductively, with the genuine
root mark and genuine original marked edges as its only constructors. -/
private inductive OriginalRootPath (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) :
    BDL26CanonicalHistoryMarks.Node S n → Prop where
  | rooted
      (hroot : BDL26CanonicalHistoryMarks.root S n ∈
        BDL26CanonicalHistoryMarks.marks S n sigma) :
      OriginalRootPath S n sigma (BDL26CanonicalHistoryMarks.root S n)
  | prepend {u v : BDL26CanonicalHistoryMarks.Node S n}
      (hedge : BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u v)
      (hpath : OriginalRootPath S n sigma v) :
      OriginalRootPath S n sigma u

/-- Complete soundness for the inductively generated ORIGINAL marked path. -/
private theorem originalRootPath_semantics (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n)
    (hp : OriginalRootPath S n sigma w) :
    BDL26CanonicalHistoryMarks.root S n ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      w ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma)
        w (BDL26CanonicalHistoryMarks.root S n) := by
  induction hp with
  | rooted hr =>
      exact ⟨hr,hr,Relation.ReflTransGen.refl⟩
  | prepend he _ ih =>
      have hm := (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma _ _).mp he
      exact ⟨ih.1,hm.2.1,(Relation.ReflTransGen.single he).trans ih.2.2⟩

/-- Completeness: every original induced path acts on rooted derivations. -/
private theorem originalRootPath_prepend_relation (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (hp : Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma) u v) :
    OriginalRootPath S n sigma v → OriginalRootPath S n sigma u := by
  induction hp with
  | refl =>
      exact fun hv => hv
  | tail _ he ih =>
      intro hv
      exact ih (@OriginalRootPath.prepend S n sigma _ _ he hv)

/-- Exact node naming acts on the first-order inductive path index. -/
private theorem originalRootPath_congr (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    {u v : BDL26CanonicalHistoryMarks.Node S n} (he : u=v)
    (hp : OriginalRootPath S n sigma v) : OriginalRootPath S n sigma u := by
  cases he
  exact hp

/-- Naturality under exact node names of a genuine original parent extension.
Both marks, the same graph edge and the lower path are transported symbolically. -/
private theorem originalRootPath_named_parent (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) (i : StepIndex (n+2))
    (u : GraphVertex S i.succ.val) (v : GraphVertex S i.castSucc.val)
    (upper lower : BDL26CanonicalHistoryMarks.Node S n)
    (hupper : upper=(⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n))
    (hlower : lower=(⟨i.castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S n))
    (hparent : parent S i.val u=some v)
    (hmark : upper ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hpath : OriginalRootPath S n sigma lower) :
    OriginalRootPath S n sigma upper := by
  subst upper
  subst lower
  have he : (decodingGraph S (n+2)).adjacent
      (⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n) ⟨i.castSucc,v⟩ := by
    apply Or.inr
    apply Or.inr
    refine ⟨i,?_⟩
    simpa only [dif_pos rfl,dif_pos True.intro] using
      (parent_interLevel_iff S (n+2) i v u).mp hparent
  have hmarkLower := (originalRootPath_semantics S n sigma _ hpath).2.1
  have hstep := (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma _ _).mpr
    ⟨he,hmark,hmarkLower⟩
  exact @OriginalRootPath.prepend S n sigma _ _ hstep hpath

/-- Typed graph edge from one original interlevel edge. The two dependent
self-casts are discharged with an arbitrary family V, not a recursive state. -/
private theorem interLevel_adjacent {depth : Nat} {V : LevelIndex depth → Type}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : DecodingGraphFamily depth V) (i : StepIndex depth)
    (u : V i.succ) (v : V i.castSucc) (h : G.interLevel i v u = true) :
    G.adjacent ⟨i.succ,u⟩ ⟨i.castSucc,v⟩ := by
  apply Or.inr
  apply Or.inr
  refine ⟨i,?_⟩
  simpa only [dif_pos rfl,dif_pos True.intro] using h

/-- Enumerations of the same finite carrier have the same Finset value. -/
private theorem fintype_dictionary_eq {N : Type} (f g : Fintype N) : f=g := by
  cases f with
  | mk sf hf =>
    cases g with
    | mk sg hg =>
      have hs : sf=sg := by
        apply Finset.ext
        intro x
        exact iff_of_true (hf x) (hg x)
      cases hs
      rfl

private theorem family_fintype_dictionary_eq {I : Type} {V : I → Type}
    (f g : ∀ i, Fintype (V i)) : f=g := by
  funext i
  exact fintype_dictionary_eq (f i) (g i)

private theorem family_decEq_dictionary_eq {I : Type} {V : I → Type}
    (d e : ∀ i, DecidableEq (V i)) : d=e := by
  funext i a b
  exact Subsingleton.elim _ _

/-- The graph record is transported, never replaced by a new graph. The Node
carrier is independent of the two dictionary parameters. The parameter
identities must be derived by the preceding general mathematical proofs. -/
private theorem graph_dictionary_transport_coherent
    {depth : Nat} {V : LevelIndex depth → Type}
    {FI1 : ∀ i, Fintype (V i)} {DE1 : ∀ i, DecidableEq (V i)}
    (FI2 : ∀ i, Fintype (V i)) (DE2 : ∀ i, DecidableEq (V i))
    (G1 : @DecodingGraphFamily depth V FI1 DE1)
    (hFI : FI1=FI2) (hDE : DE1=DE2) :
    let hType : @DecodingGraphFamily depth V FI1 DE1 =
        @DecodingGraphFamily depth V FI2 DE2 :=
      congrArg₂ (fun (f : ∀ i, Fintype (V i))
        (d : ∀ i, DecidableEq (V i)) => @DecodingGraphFamily depth V f d) hFI hDE
    let G2 := Eq.mp hType G1
    (∀ (i : StepIndex depth) (v : V i.castSucc) (u : V i.succ),
      @DecodingGraphFamily.interLevel depth V FI1 DE1 G1 i v u =
        @DecodingGraphFamily.interLevel depth V FI2 DE2 G2 i v u) ∧
    (∀ u v : Σ i : LevelIndex depth, V i,
      @DecodingGraphFamily.adjacent depth V FI1 DE1 G1 u v ↔
        @DecodingGraphFamily.adjacent depth V FI2 DE2 G2 u v) := by
  cases hFI
  cases hDE
  constructor
  · intro i v u
    rfl
  · intro u v
    exact Iff.rfl

/-- Coherent inter-level introduction on the SAME supplied graph. FI1/DE1
are captured from G1's original type, not synthesized as a replacement pair.
The explicit pair is propositionally identified, the record is transported,
and the resulting edge is transported BACK to G1's original adjacency. -/
private theorem interLevel_adjacent_dictionary_coherent
    {depth : Nat} {V : LevelIndex depth → Type}
    {FI1 : ∀ i, Fintype (V i)} {DE1 : ∀ i, DecidableEq (V i)}
    (FI2 : ∀ i, Fintype (V i)) (DE2 : ∀ i, DecidableEq (V i))
    (G1 : @DecodingGraphFamily depth V FI1 DE1)
    (i : StepIndex depth) (u : V i.succ) (v : V i.castSucc)
    (h : @DecodingGraphFamily.interLevel depth V FI1 DE1 G1 i v u = true) :
    @DecodingGraphFamily.adjacent depth V FI1 DE1 G1 ⟨i.succ,u⟩ ⟨i.castSucc,v⟩ := by
  have hFI : FI1=FI2 := family_fintype_dictionary_eq FI1 FI2
  have hDE : DE1=DE2 := family_decEq_dictionary_eq DE1 DE2
  let hType : @DecodingGraphFamily depth V FI1 DE1 =
      @DecodingGraphFamily depth V FI2 DE2 :=
    congrArg₂ (fun (f : ∀ j, Fintype (V j))
      (d : ∀ j, DecidableEq (V j)) => @DecodingGraphFamily depth V f d) hFI hDE
  let G2 : @DecodingGraphFamily depth V FI2 DE2 := Eq.mp hType G1
  have hc := graph_dictionary_transport_coherent FI2 DE2 G1 hFI hDE
  have h2 : @DecodingGraphFamily.interLevel depth V FI2 DE2 G2 i v u = true :=
    (hc.1 i v u).symm.trans h
  have he2 := @interLevel_adjacent depth V FI2 DE2 G2 i u v h2
  exact (hc.2 ⟨i.succ,u⟩ ⟨i.castSucc,v⟩).mpr he2

/-- Full component representation from semantics, not a supplied target member.
U completeness is ordinary finite enumeration completeness. No Fintype or
DecidableEq instance on N is required in this theorem. -/
private theorem complete_component_representation_eq {N : Type}
    (K M U : Finset N) (R : N → N → Prop) (root : N)
    [Decidable (root ∈ M)]
    [DecidablePred (fun w => w ∈ M ∧ Relation.ReflTransGen R w root)]
    (hU : ∀ w, w ∈ U)
    (hK : ∀ w, w ∈ K ↔ root ∈ M ∧ w ∈ M ∧ Relation.ReflTransGen R w root) :
    K = if root ∈ M then
      U.filter (fun w => w ∈ M ∧ Relation.ReflTransGen R w root) else ∅ := by
  apply Finset.ext
  intro w
  by_cases hr : root ∈ M
  · simpa [hr,hU w] using hK w
  · simpa [hr] using hK w

private theorem originalRootPath_mem_iff (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n) :
    OriginalRootPath S n sigma w ↔
      w ∈ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  constructor
  · intro hp
    exact (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mpr
      (originalRootPath_semantics S n sigma w hp)
  · intro hw
    obtain ⟨hr,_hm,hp⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mp hw
    exact originalRootPath_prepend_relation S n sigma w
      (BDL26CanonicalHistoryMarks.root S n) hp (@OriginalRootPath.rooted S n sigma hr)

private theorem originalRootPath_parented_base (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (v : GraphVertex S 2) (hv : v ∈ BDL26CanonicalHistoryMarks.baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    OriginalRootPath S n sigma (BDL26CanonicalHistoryMarks.physicalNode S n 0 v) := by
  have hr := (BDL26CanonicalHistoryMarks.root_marked_iff_parented_base S n sigma).mpr
    ⟨v,hv,u,hp⟩
  have hpath := BDL26CanonicalHistoryMarks.parented_base_root_path S n sigma v hv u hp
  exact originalRootPath_prepend_relation S n sigma _
    (BDL26CanonicalHistoryMarks.root S n) hpath (@OriginalRootPath.rooted S n sigma hr)

/-- Direct introduction into the ORIGINAL induced relation. The graph,
marks and complete Node endpoints remain symbolic throughout this proof. -/
private theorem canonical_marked_edge_intro (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (he : (decodingGraph S (n+2)).adjacent u v)
    (hu : u ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hv : v ∈ BDL26CanonicalHistoryMarks.marks S n sigma) :
    BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u v :=
  (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma u v).mpr ⟨he,hu,hv⟩

/-- One genuine graph edge and the original upper mark prepend the already
proved original lower path. No dependent level/cell or parent telescope is
specialized by the caller, and no upper-root conclusion is a premise. -/
private theorem originalRootPath_graph_extend (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (he : (decodingGraph S (n+2)).adjacent u v)
    (hu : u ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hv : OriginalRootPath S n sigma v) : OriginalRootPath S n sigma u := by
  have hm := (originalRootPath_semantics S n sigma v hv).2.1
  have he' := canonical_marked_edge_intro S n sigma u v he hu hm
  exact @OriginalRootPath.prepend S n sigma u v he' hv

private theorem actual_base_original_root_path (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    OriginalRootPath S 2 sigma (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by
  have hmarked := actual_base_retained_marked S sigma hbase
  have hpath := originalRootPath_parented_base S 2 sigma
    (zVertex S 1 (baseRetainedZ S)) hmarked
    (zVertex S 0 (seedZ S)) (base_retained_parent S)
  exact originalRootPath_congr S 2 sigma
    (actualBaseNode_physical S (zVertex S 1 (baseRetainedZ S))) hpath

/-- The actual nonzero base mark reaches the original root. -/
theorem actual_base_Z_root_member (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)
      (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by
  have hpath := actual_base_original_root_path S sigma hbase
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 sigma) =
      OriginalRootPath S 2 sigma := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 sigma w).symm)
  have hnode := congrFun hcomponent (actualBaseNode S (zVertex S 1 (baseRetainedZ S)))
  rw [hnode]
  exact hpath

/-- The actual stored mid-level input supplies the actual syndrome-owner mark. -/
theorem actual_mid_Z_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    actualMidNode S (zVertex S 2 (r2 S)) ∈
      BDL26CanonicalHistoryMarks.marks S 2 sigma := by
  classical
  let v3 : GraphVertex S 3 := zVertex S 2 (r2 S)
  obtain ⟨b,hb⟩ := lower3_retained_nonzero S
  let p := ((A S).induced.zPairEquiv (r2 S,b)).val
  have howner : BDL26CanonicalHistoryMarks.syndromeOwner S 2
      (0 : StepIndex 2) p = v3 := by
    change BDL26RXDecoderAdapter.vertexEquiv (state S 2).presentation
      ((A S).topCenter p) = zVertex S 2 (r2 S)
    dsimp only [p]
    rw [(A S).topCenter_coarse_pair]
    rfl
  have hinput : (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (0 : StepIndex 2)).input.val p ≠ 0 := by
    have hmid' : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
        (0 : StepIndex 2).succ = lower3 S := hmid
    have hi : (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (0 : StepIndex 2)).input =
        lower3 S :=
      (BDL26CanonicalHistoryMarks.outputAt_input S 2 sigma (0 : StepIndex 2)).trans hmid'
    have hv : (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (0 : StepIndex 2)).input.val p =
        (lower3 S).val p :=
      congrArg (fun word : (CF S).Syndrome level3 => word.val p) hi
    exact fun hz => hb (hv.symm.trans hz)
  have habove : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p ∈
      BDL26CanonicalHistoryMarks.aboveMarks S 2 sigma (0 : StepIndex 2) := by
    unfold BDL26CanonicalHistoryMarks.aboveMarks
    exact @BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome
      4 (FamilyX S 4) (FamilyQ S 4) (FamilyZ S 4)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.xFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.qFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.zFintype)
      (indexedDecoderData S 4) (LevelTwoHistory.physicalStep (0 : StepIndex 2))
      (GraphVertex S 3)
      (BDL26DecodingGraph.graphVertexFintype S 3)
      (BDL26DecodingGraph.graphVertexDecidableEq S 3)
      (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (0 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.pieceOwner S 2 sigma (0 : StepIndex 2)) p hinput
  have hphysical : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p ∈
      BDL26CanonicalHistoryMarks.physicalMarks S 2 sigma (0 : StepIndex 2).succ :=
    predicate_transport
      (fun M : Finset (GraphVertex S 3) =>
        BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p ∈ M)
      (BDL26CanonicalHistoryMarks.physicalMarks_step S 2 sigma (0 : StepIndex 2)) habove
  have hm : BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma :=
    (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 sigma (0 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p)).mpr hphysical
  have he : BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) =
        actualMidNode S v3 :=
    (congrArg (fun v : GraphVertex S 3 =>
      BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : LevelIndex 2) v) howner).trans
        (actualMidNode_physical S v3).symm
  exact he ▸ hm

/-- Only the original adjacent-parent identity, on typed literal vertices. -/
theorem mid_Z_parent (S : OddScale) :
    parent S 2 (zVertex S 2 (r2 S)) = some (zVertex S 1 (baseRetainedZ S)) := by
  change rzParent (state S 1).presentation
    (state S 1).admissible.toTannerSquareAdmissible S
    (Vertex.z (r2 S)) = some (Vertex.z (baseRetainedZ S))
  rfl

private theorem retained_Z_original_root_path (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    OriginalRootPath S 2 sigma (actualMidNode S (zVertex S 2 (r2 S))) := by
  let u : GraphVertex S 3 := zVertex S 2 (r2 S)
  let v : GraphVertex S 2 := zVertex S 1 (baseRetainedZ S)
  have hmarked := actual_mid_Z_marked S sigma hmid
  have hlower := actual_base_original_root_path S sigma hbase
  have hupper := originalRootPath_named_parent S 2 sigma (2 : StepIndex 4) u v
    (actualMidNode S u) (actualBaseNode S v)
    (actualMidNode_literal S u) (actualBaseNode_literal S v)
    (mid_Z_parent S) hmarked hlower
  exact hupper

theorem retained_Z_actual_root_member (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)
      (actualMidNode S (zVertex S 2 (r2 S))) := by
  have hpath := retained_Z_original_root_path S sigma hbase hmid
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 sigma) =
      OriginalRootPath S 2 sigma := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 sigma w).symm)
  have hnode := congrFun hcomponent (actualMidNode S (zVertex S 2 (r2 S)))
  rw [hnode]
  exact hpath

private theorem actual_retained_original_root_path (S : OddScale) :
    OriginalRootPath S 2 (upper4 S) (actualMidNode S (zVertex S 2 (r2 S))) :=
  retained_Z_original_root_path S (upper4 S) (actual_base_input S) (actual_mid_input S)

/-- The concrete real lower Z ancestor, with the actual stored snapshots. -/
theorem actual_retained_root_member (S : OddScale) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S))
      (actualMidNode S (zVertex S 2 (r2 S))) := by
  have hpath := actual_retained_original_root_path S
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)) =
      OriginalRootPath S 2 (upper4 S) := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 (upper4 S) w).symm)
  have hnode := congrFun hcomponent (actualMidNode S (zVertex S 2 (r2 S)))
  rw [hnode]
  exact hpath

/-- The real last stored output has the original top input. -/
theorem actual_top_output_input (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2)).input = sigma := by
  have hot := BDL26CanonicalHistoryMarks.outputAt_top S 1 sigma
  change BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2) =
    actualStep S 4 (3 : StepIndex 4) sigma at hot
  exact (congrArg AssemblyStepOutput.input hot).trans
    ((actualStep_relation S 4 (3 : StepIndex 4)).input_eq sigma)

/-- A nonzero genuine top coordinate marks its actual Z-cylinder owner. -/
theorem actual_top_Z_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S)
    (hp : sigma.val (⟨z,v⟩ : FamilyZ S 4 level4) ≠ 0) :
    actualTopNode S (zVertex S 3 z) ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma := by
  have hi : (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2)).input.val
      (⟨z,v⟩ : FamilyZ S 4 level4) = sigma.val ⟨z,v⟩ :=
    congrArg (fun word : (CF S).Syndrome level4 => word.val ⟨z,v⟩)
      (actual_top_output_input S sigma)
  have habove : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈
      BDL26CanonicalHistoryMarks.aboveMarks S 2 sigma (1 : StepIndex 2) := by
    unfold BDL26CanonicalHistoryMarks.aboveMarks
    exact @BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome
      4 (FamilyX S 4) (FamilyQ S 4) (FamilyZ S 4)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.xFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.qFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.zFintype)
      (indexedDecoderData S 4) (LevelTwoHistory.physicalStep (1 : StepIndex 2))
      (GraphVertex S 4)
      (BDL26DecodingGraph.graphVertexFintype S 4)
      (BDL26DecodingGraph.graphVertexDecidableEq S 4)
      (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.pieceOwner S 2 sigma (1 : StepIndex 2)) (⟨z,v⟩ : FamilyZ S 4 level4) (fun hz => hp (hi.symm.trans hz))
  have hphysical : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈
      BDL26CanonicalHistoryMarks.physicalMarks S 2 sigma (1 : StepIndex 2).succ :=
    predicate_transport
      (fun M : Finset (GraphVertex S 4) =>
        BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈ M)
      (BDL26CanonicalHistoryMarks.physicalMarks_step S 2 sigma (1 : StepIndex 2)) habove
  have hm : BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4)) ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma :=
    (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 sigma (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4))).mpr hphysical
  have he : BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) ⟨z,v⟩) =
        actualTopNode S (zVertex S 3 z) :=
    (congrArg (fun w : GraphVertex S 4 =>
      BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) w)
        (top_owner_apply S z v)).trans (actualTopNode_physical S (zVertex S 3 z)).symm
  exact he ▸ hm

/-- Literal parent of an actual retained RX Z coordinate. -/
theorem retained_top_parent (S : OddScale) (b : Fin 2) :
    parent S 3 (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val) =
      some (zVertex S 2 (r2 S)) := by
  change rxParent (state S 2).presentation S
    (Vertex.z (Sum.inr (r2 S,b))) = some (Vertex.z (r2 S))
  rfl

private theorem nonzero_retained_original_root_path (S : OddScale) (b : Fin 2)
    (hb : (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val ≠ 0) :
    OriginalRootPath S 2 (upper4 S)
      (actualTopNode S (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val)) := by
  classical
  let z := ((A S).induced.zPairEquiv (r2 S,b)).val
  let v := rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
  have hup : (upper4 S).val (⟨z,v⟩ : FamilyZ S 4 level4) ≠ 0 := by
    rw [upper4_val,selected_top_map2_apply]
    simpa [v,z] using hb
  let u : GraphVertex S 4 := zVertex S 3 z
  let w : GraphVertex S 3 := zVertex S 2 (r2 S)
  have hmarked := actual_top_Z_marked S (upper4 S) z v hup
  have hlower := actual_retained_original_root_path S
  have hupper := originalRootPath_named_parent S 2 (upper4 S) (3 : StepIndex 4) u w
    (actualTopNode S u) (actualMidNode S w)
    (actualTopNode_literal S u) (actualMidNode_castSucc_literal S w)
    (retained_top_parent S b) hmarked hlower
  exact hupper

/-- Nonzero retained input marks the actual top node, whose original parent
is the already-rooted lower Z node. Closed top corrections do not affect it. -/
theorem nonzero_retained_top_in_root (S : OddScale) (b : Fin 2)
    (hb : (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val ≠ 0) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S))
      (actualTopNode S (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val)) := by
  have hpath := nonzero_retained_original_root_path S b hb
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)) =
      OriginalRootPath S 2 (upper4 S) := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 (upper4 S) w).symm)
  have hnode := congrFun hcomponent (actualTopNode S (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val))
  rw [hnode]
  exact hpath

theorem eta_retained_value (S : OddScale) (b : Fin 2) :
    eta S ((A S).induced.zPairEquiv (r2 S,b)).val =
      (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val := by
  classical
  let z : FamilyZ S 4 level3 := ((A S).induced.zPairEquiv (r2 S,b)).val
  let P : FamilyZ S 4 level3 → Prop := fun p => actualTopNode S (zVertex S 3 p) ∈
    BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
  let Q : FamilyZ S 4 level3 → Prop := fun p =>
    OriginalRootPath S 2 (upper4 S) (actualTopNode S (zVertex S 3 p))
  have hwhole := @selectedWord_congr_iff (FamilyZ S 4 level3) P Q
    (inferInstance : DecidablePred P) (inferInstance : DecidablePred Q)
    (fun p => (originalRootPath_mem_iff S 2 (upper4 S)
      (actualTopNode S (zVertex S 3 p))).symm) (lower3 S).val
  have hsemantic := @selectedWord_preserves (FamilyZ S 4 level3) Q
    (inferInstance : DecidablePred Q) (lower3 S).val z
    (nonzero_retained_original_root_path S b)
  have horiginal : eta S z = selectedWord P (lower3 S).val z := rfl
  exact horiginal.trans ((congrFun hwhole z).trans hsemantic)

theorem eta_retained_imbalance (S : OddScale) :
    eta S ((A S).induced.zPairEquiv (r2 S,0)).val +
      eta S ((A S).induced.zPairEquiv (r2 S,1)).val = 1 := by
  exact (congrArg₂ (fun a b : BDL26Field => a+b)
    (eta_retained_value S 0) (eta_retained_value S 1)).trans (lower3_retained_imbalance S)

/-- The masked lower word is not assumed valid; nonvalidity is proved. -/
theorem eta_not_boundary (S : OddScale) : eta S ∉ LinearMap.range (d3 S) := by
  apply zero_aux_imbalance_not_boundary S (eta S) (eta_X_query_zero S)
    (eta_Q_query_zero S) (r2 S)
  intro he
  have hi := eta_retained_imbalance S
  rw [he,ZModModule.add_self] at hi
  exact zero_ne_one hi

/-- Direct failure of the current literal original-root witness-foot property. -/
theorem actual_top_witness_not_boundary (S : OddScale) :
    topWitness S (upper4 S) ∉
      LinearMap.range ((CF S).coboundary1 level4) := by
  intro h
  rw [topWitness_factor] at h
  exact eta_not_boundary S (top_RZ_reflects_boundary S (eta S) h)

/-- Uniform in every OddScale. The input is an actual valid Syndrome and the
history is the real canonical history stopping at C2. No logical-instability
premise or claim is added, and no change to the frozen ALL contract is made. -/
theorem exists_actual_original_root_witness_not_boundary (S : OddScale) :
    ∃ sigma : (indexedFamily S 4).Syndrome (4 : LevelIndex 4),
      (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val ≠ 0 ∧
      topWitness S sigma ∉
        LinearMap.range ((indexedFamily S 4).coboundary1 (4 : LevelIndex 4)) := by
  refine ⟨upper4 S,?_,actual_top_witness_not_boundary S⟩
  rw [actual_base_input]
  exact gamma2_nonzero S

/-- Explicit concrete instance requested before the uniform strengthening. -/
theorem scaleFive_actual_original_root_witness_not_boundary :
    ∃ sigma : (indexedFamily scaleFive 4).Syndrome (4 : LevelIndex 4),
      (BDL26CanonicalHistoryMarks.baseInput scaleFive 2 sigma).val ≠ 0 ∧
      topWitness scaleFive sigma ∉
        LinearMap.range ((indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4)) :=
  exists_actual_original_root_witness_not_boundary scaleFive

end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample

/-! ## Failure of original root-only RZ mask commutation

The genuine RX Q query marks a lower owner connected to the original root.
Its corresponding upper RZ owner is an unparented positive-dimensional cell,
so the same root component deletes its nonzero RZ image. This is an absolute
syndrome-mask obstruction, not a localized error-difference transport claim.
-/
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators

noncomputable section

/-- The literal C3 owner fibre mask of the same original depth-four root. -/
noncomputable def rootMaskMidRegion (S : OddScale) :
    Finset (FamilyZ S 4 level3) :=
  Finset.univ.filter (fun p =>
    actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S))

noncomputable def rootMaskMidWord (S : OddScale) : Word3 S :=
  maskWord (rootMaskMidRegion S) (lower3 S).val

theorem rootMask_localQ_query_nonzero (S : OddScale) :
    localQuery S (q2 S) ≠ 0 := by
  rw [localQuery,localSeed_at_q2]
  exact terminalSyndrome_ne_zero S (q2 S) (r2 S) (q2_incidence S)

theorem rootMask_nonzero_Q_coordinate (S : OddScale) :
    ∃ p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S)),
      (lower3 S).val p.val ≠ 0 := by
  by_contra h
  push_neg at h
  apply rootMask_localQ_query_nonzero S
  rw [← lower3_Q_query S (q2 S)]
  funext p
  exact h p

/-- The real stored C3 input, rather than a supplied root certificate, marks its owner. -/
theorem rootMask_mid_input_owner_marked (S : OddScale)
    (p : FamilyZ S 4 level3) (hp : (lower3 S).val p ≠ 0) :
    actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S) := by
  have hi : (BDL26CanonicalHistoryMarks.outputAt S 2 (upper4 S)
      (0 : StepIndex 2)).input = lower3 S :=
    (BDL26CanonicalHistoryMarks.outputAt_input S 2 (upper4 S) (0 : StepIndex 2)).trans
      (actual_mid_input S)
  have hin : (BDL26CanonicalHistoryMarks.outputAt S 2 (upper4 S)
      (0 : StepIndex 2)).input.val p ≠ 0 := by
    intro hz
    exact hp ((congrArg (fun word : (CF S).Syndrome level3 => word.val p) hi).symm.trans hz)
  change BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : StepIndex 2).succ
    (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S)
  apply (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 (upper4 S)
    (0 : StepIndex 2).succ _).mpr
  rw [BDL26CanonicalHistoryMarks.physicalMarks_step]
  apply (BDL26CanonicalHistoryMarks.mem_aboveMarks S 2 (upper4 S) (0 : StepIndex 2) _).mpr
  exact Or.inl ⟨p,rfl,hin⟩

theorem rootMask_Q_coordinate_owner (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p.val =
      @Vertex.q (state S 2).presentation (q2 S) := by
  change BDL26RXDecoderAdapter.vertexEquiv (state S 2).presentation
    ((A S).topCenter p.val) = @Vertex.q (state S 2).presentation (q2 S)
  rw [((A S).topCenter_q_iff (q2 S) p.val).mp p.property]
  rfl

/-- Genuine marked horizontal Q-to-Z reachability, consumed by both finite-root
membership and the complete original-mask representation. -/
private theorem rootMask_Q_owner_original_path (S : OddScale) :
    OriginalRootPath S 2 (upper4 S)
      (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S))) := by
  obtain ⟨p,hp⟩ := rootMask_nonzero_Q_coordinate S
  have hm : actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S) := by
    rw [← rootMask_Q_coordinate_owner S p]
    apply rootMask_mid_input_owner_marked S p.val
    exact hp
  have he : (decodingGraph S 4).adjacent
      (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)))
      (actualMidNode S (zVertex S 2 (r2 S))) := by
    apply Or.inl
    change (state S 2).presentation.qz (q2 S) (r2 S) = true
    exact q2_incidence S
  exact originalRootPath_graph_extend S 2 (upper4 S)
    (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)))
    (actualMidNode S (zVertex S 2 (r2 S))) he hm (actual_retained_original_root_path S)

/-- A genuine horizontal incidence joins the marked Q owner to the rooted Z owner. -/
theorem rootMask_Q_owner_root_member (S : OddScale) :
    actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S) := by
  have hpath := rootMask_Q_owner_original_path S
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)) =
      OriginalRootPath S 2 (upper4 S) := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 (upper4 S) w).symm)
  have hnode := congrFun hcomponent
    (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)))
  rw [hnode]
  exact hpath

/-- Every Q coordinate in that fibre survives the genuine lower owner mask. -/
theorem rootMask_mid_Q_value (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    rootMaskMidWord S p.val = (lower3 S).val p.val := by
  classical
  let P : FamilyZ S 4 level3 → Prop := fun z => actualMidNode S
    (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
  let Q : FamilyZ S 4 level3 → Prop := fun z => OriginalRootPath S 2 (upper4 S)
    (actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z))
  have hwhole := @selectedWord_congr_iff (FamilyZ S 4 level3) P Q
    (inferInstance : DecidablePred P) (inferInstance : DecidablePred Q)
    (fun z => (originalRootPath_mem_iff S 2 (upper4 S)
      (actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z))).symm)
    (lower3 S).val
  have hpath : Q p.val := originalRootPath_congr S 2 (upper4 S)
    (congrArg (actualMidNode S) (rootMask_Q_coordinate_owner S p))
    (rootMask_Q_owner_original_path S)
  have hsemantic := @selectedWord_preserves (FamilyZ S 4 level3) Q
    (inferInstance : DecidablePred Q) (lower3 S).val p.val (fun _ => hpath)
  have horiginal : rootMaskMidWord S p.val = selectedWord P (lower3 S).val p.val :=
    (mask_filter_apply P (lower3 S).val p.val).trans
      (selectedWord_apply P (lower3 S).val p.val).symm
  exact horiginal.trans ((congrFun hwhole p.val).trans hsemantic)

/-- Original root-only selected-map2 commutation already fails at the actual top RZ step. -/
theorem rootMask_RZ_map2_failure (S : OddScale) :
    topWitness S (upper4 S) ≠
      ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) := by
  let Z := rzData S 4 (3 : StepIndex 4) (by decide)
  have hleft (word : Word3 S) : RZCoarseGraining.RZCoarseGrainingData.topParity Z
      (((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 word) = word := by
    rw [selectedMap_eq]
    exact RZCoarseGraining.topParity_rzMap_map2 Z word
  have hinj (a b : Word3 S)
      (hab : ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 a =
        ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 b) : a = b :=
    (hleft a).symm.trans
      ((congrArg (RZCoarseGraining.RZCoarseGrainingData.topParity Z) hab).trans (hleft b))
  have hrestrict_eval {I : Type} [Fintype I]
      (Y : Finset I) (word : Word BDL26Field I) (p : LocalRegionIndex Y) :
      (restrictWordLinear Y word) p = word p.val := rfl
  have hneq : eta S ≠ rootMaskMidWord S := by
    intro hsame
    obtain ⟨p,hp⟩ := rootMask_nonzero_Q_coordinate S
    have hval : eta S p.val = rootMaskMidWord S p.val :=
      congrArg (fun word : Word3 S => word p.val) hsame
    have hz0 := congrArg
      (fun word : LocalRegionIndex ((LQ S).syndromeRegion (q2 S)) → BDL26Field => word p)
      (eta_Q_query_zero S (q2 S))
    have hz := (hrestrict_eval ((LQ S).syndromeRegion (q2 S)) (eta S) p).symm.trans hz0
    exact hp ((rootMask_mid_Q_value S p).symm.trans (hval.symm.trans hz))
  intro he
  exact hneq (hinj (eta S) (rootMaskMidWord S) ((topWitness_factor S).symm.trans he))

/-- The exact valid depth-four input has nonzero actual C2 readout and both original-root obstructions. -/
theorem rootMask_actual_nonzero_full_obstruction (S : OddScale) :
    (BDL26CanonicalHistoryMarks.baseInput S 2 (upper4 S)).val ≠ 0 ∧
      topWitness S (upper4 S) ≠
        ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) ∧
      topWitness S (upper4 S) ∉ LinearMap.range ((CF S).coboundary1 level4) := by
  constructor
  · rw [actual_base_input]
    exact gamma2_nonzero S
  · exact ⟨rootMask_RZ_map2_failure S,actual_top_witness_not_boundary S⟩

end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
