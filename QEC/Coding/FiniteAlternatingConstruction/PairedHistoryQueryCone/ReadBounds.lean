import QEC.Coding.FiniteAlternatingConstruction.PairedHistoryQueryCone.LocalReads

/-! # Coordinate budgets for actual selector queries -/
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

/-- Reversing the query graph does not assert symmetric directed distance. -/
def reverseGraph {V : Type} [Fintype V] [DecidableEq V] (G : DirectedGraph V) :
    DirectedGraph V where
  edge u v := G.edge v u
  loopless := G.loopless

theorem incomingTwo_subset {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (v : V) :
    xiIndexSet G v 2 ⊆ forwardTwo (reverseGraph G) v := by
  intro u hu
  have hp := distance_le_two_mem_forwardTwo G u v (Finset.mem_filter.mp hu).2
  rcases (mem_forwardTwo G u v).mp hp with he | he | ⟨w,huw,hwv⟩
  · exact (mem_forwardTwo _ _ _).mpr (Or.inl he.symm)
  · exact (mem_forwardTwo _ _ _).mpr (Or.inr (Or.inl he))
  · exact (mem_forwardTwo _ _ _).mpr (Or.inr (Or.inr ⟨w,hwv,huw⟩))

private theorem directed_adjacent (P : TannerSquarePresentation) (u v : Vertex P)
    (he : (tannerLevel P).graph.edge u v = true) : tannerAdjacent P v u := by
  rw [tannerLevel_edge] at he
  cases u <;> cases v <;> simp_all [tannerDirected,tannerAdjacent]

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem actual_inNeighbors_card_le (h : i.val % 2 = 0) (v : Owners S depth i) :
    (outNeighbors (reverseGraph (rxData S depth i h).levelGraph.graph) v).card ≤ 7 := by
  let P := (state S i.val).presentation
  have hb : (outNeighbors (reverseGraph (rxData S depth i h).levelGraph.graph) v).card ≤
      tannerDegree P (vertexEquiv P v) := by
    unfold tannerDegree
    rw [Fintype.card_subtype]
    apply Finset.card_le_card_of_injOn (vertexEquiv P)
    · intro w hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have he := (Finset.mem_filter.mp hw).2
      change (rxData S depth i h).levelGraph.graph.edge w v = true at he
      rw [rxData_graph_edge S depth i h] at he
      exact directed_adjacent P _ _ he
    · exact (vertexEquiv P).injective.injOn
  exact hb.trans (state_tannerDegree_le S i.val _)

theorem rx_incomingTwo_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    (xiIndexSet (rxData S depth i h).levelGraph.graph v 2).card ≤ 57 :=
  (Finset.card_le_card (incomingTwo_subset _ v)).trans
    (forwardTwo_card_le _ (actual_inNeighbors_card_le S depth i h) v)

/-- The full actual syndrome fibre, identified with its raw constructor chart. -/
theorem rx_region_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v).card ≤
      localCoordinateBound S := by
  let E := BDL26RXQConcreteCoherence.physicalZEquiv S depth i h
  let P := (state S i.val).presentation
  have hc : ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v).card ≤
      Fintype.card {r : BDL26RXLocalReplacement.RX2 P S //
        BDL26ReplacementSupport.rxSyndromeOwner P S r = vertexEquiv P v} := by
    rw [Fintype.card_subtype]
    apply Finset.card_le_card_of_injOn E.symm
    · intro p hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have ht := BDL26RXQConcreteCoherence.topCenter_chart S depth i h (E.symm p)
      rw [E.apply_symm_apply] at ht
      rw [(rxXiLocalComplex_region_mem_iff _ _ _).mp hp] at ht
      exact ht.symm
    · exact E.symm.injective.injOn
  exact hc.trans (rxSyndromeFiber_card_le P (BDL26BoundedValence.state_boundedValence S i.val)
    S (vertexEquiv P v))

private theorem transported_region_card {A B L : Type} [Fintype A] [Fintype B]
    (h : A = B) (f : L → Finset A) (g : L → Finset B) (hf : HEq f g) (v : L) :
    (f v).card = (g v).card := by
  cases h
  cases hf
  rfl

theorem rz_region_card (h : ¬ i.val % 2 = 0)
    (z : FamilyZ S depth i.castSucc) :
    ((rzData S depth i h).coarseRegion z).card ≤ localCoordinateBound S := by
  have he : state S (i.val+1) = rzState S (state S i.val) := by
    change nextState S i.val (state S i.val) = _
    exact if_neg h
  have hc := transported_region_card
    (congrArg (fun C : ConstructionState => C.presentation.Z) he)
    (rzData S depth i h).coarseRegion
    (BDL26RZConcreteParity.blockRegion (state S i.val).presentation S)
    (rzData_coordinates S depth i h).1 z
  rw [hc]
  have hr := rzSyndromeFiber_card_le (state S i.val).presentation
    (state S i.val).admissible.toTannerSquareAdmissible
    (BDL26BoundedValence.state_boundedValence S i.val) S z
  have hcard : Fintype.card {c : BDL26RZLocalReplacement.RZZ (state S i.val).presentation S //
      BDL26ReplacementSupport.rzSyndromeOwner (state S i.val).presentation S c = z} =
        (BDL26RZConcreteParity.blockRegion (state S i.val).presentation S z).card := by
    apply Fintype.card_of_subtype
    intro c
    simp only [BDL26RZConcreteParity.blockRegion, BDL26ReplacementSupport.fiberRegion,
      Finset.mem_filter, Finset.mem_univ, true_and, BDL26ReplacementSupport.rzSyndromeOwner]
  exact hcard.symm.trans_le hr

/-- A backward query block includes at most 57 full local syndrome fibres. -/
def queryBlockBound (S : OddScale) : Nat := 57 * localCoordinateBound S

theorem rxOwnerRead_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    (rxOwnerRead S depth i h v).card ≤ queryBlockBound S := by
  have hb := Finset.card_biUnion_le_card_mul
    (xiIndexSet (rxData S depth i h).levelGraph.graph v 2)
    (fun w => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion w)
    (localCoordinateBound S) (fun w _ => rx_region_card S depth i h w)
  exact hb.trans (Nat.mul_le_mul_right _ (rx_incomingTwo_card S depth i h v))

theorem ownerRead_card (v : Owners S depth i) :
    (ownerRead S depth i v).card ≤ queryBlockBound S := by
  by_cases h : i.val % 2 = 0
  · simpa only [ownerRead,dif_pos h] using rxOwnerRead_card S depth i h v
  · simp only [ownerRead,dif_neg h]
    cases v with
    | inl x => simp
    | inr v => cases v with
      | inl q => simp
      | inr z =>
          exact (rz_region_card S depth i h z).trans (by
            unfold queryBlockBound
            omega)

theorem coarseRead_card (z : FamilyZ S depth i.castSucc) :
    (coarseRead S depth i z).card ≤ queryBlockBound S := by
  by_cases h : i.val % 2 = 0
  · simpa only [coarseRead,dif_pos h,readRegion,rxOwnerRead] using
      rxOwnerRead_card S depth i h ((rxData S depth i h).coarseCenter z)
  · simp only [coarseRead,dif_neg h]
    exact (rz_region_card S depth i h z).trans (by unfold queryBlockBound; omega)

theorem ownerReaders_card (p : FamilyZ S depth i.succ) :
    ((Finset.univ : Finset (Owners S depth i)).filter
      (fun v => p ∈ ownerRead S depth i v)).card ≤ 57 := by
  by_cases h : i.val % 2 = 0
  · have hs : ((Finset.univ : Finset (Owners S depth i)).filter
        (fun v => p ∈ ownerRead S depth i v)) ⊆
        forwardTwo (rxData S depth i h).levelGraph.graph ((rxData S depth i h).topCenter p) := by
      intro v hv
      have hp := (Finset.mem_filter.mp hv).2
      rw [ownerRead,dif_pos h] at hp
      exact distance_le_two_mem_forwardTwo _ _ _ ((mem_rxOwnerRead S depth i h v p).mp hp)
    exact (Finset.card_le_card hs).trans
      (forwardTwo_card_le _ (actual_outNeighbors_card_le S depth i h) _)
  · have hs : ((Finset.univ : Finset (Owners S depth i)).filter
        (fun v => p ∈ ownerRead S depth i v)) ⊆
        {Sum.inr (Sum.inr (rzBlockOwner S depth i h p))} := by
      intro v hv
      have hp := (Finset.mem_filter.mp hv).2
      rw [ownerRead,dif_neg h] at hp
      cases v with
      | inl x => simpa using hp
      | inr v => cases v with
        | inl q => simpa using hp
        | inr z =>
            have he := rzBlockOwner_eq S depth i h p z hp
            simp only [Finset.mem_singleton]
            exact congrArg (fun t => Sum.inr (Sum.inr t)) he.symm
    exact (Finset.card_le_card hs).trans (by simp)

theorem affected_card (U : Finset (FamilyZ S depth i.succ)) :
    (affected S depth i U).card ≤ 57 * U.card := by
  have he : affected S depth i U = U.biUnion (fun p =>
      (Finset.univ : Finset (Owners S depth i)).filter
        (fun v => p ∈ ownerRead S depth i v)) := by
    ext v
    simp only [affected,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion]
  rw [he]
  exact (Finset.card_biUnion_le_card_mul U _ 57
    (fun p _ => ownerReaders_card S depth i p)).trans_eq (Nat.mul_comm _ _)

theorem correctionQueries_card (U : Finset (FamilyZ S depth i.succ)) :
    (correctionQueries S depth i U).card ≤ queryBlockBound S * (57 * U.card) := by
  exact (Finset.card_biUnion_le_card_mul _ _ (queryBlockBound S)
    (fun v _ => ownerRead_card S depth i v)).trans
      (by have h := affected_card S depth i U; nlinarith)

theorem liftQueries_card (A : Finset (FamilyZ S depth i.castSucc)) :
    (liftQueries S depth i A).card ≤ queryBlockBound S * A.card := by
  exact (Finset.card_biUnion_le_card_mul A _ (queryBlockBound S)
    (fun z _ => coarseRead_card S depth i z)).trans_eq (Nat.mul_comm _ _)

end QEC.Coding.BDL26PairedHistoryQueryCone
