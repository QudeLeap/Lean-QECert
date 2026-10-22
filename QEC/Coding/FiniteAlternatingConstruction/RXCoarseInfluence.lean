import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter

/-!
# Actual RX coarse-output influence of an upper basis perturbation

[BDL26, Definition locally computable, Section 4]. The finite influence set
below uses the existing radius-two directed neighborhood and actual syndrome
regions. It bounds differences of the canonical coarse syndrome only.
-/

noncomputable section
namespace QEC.Coding.BDL26RXCoarseInfluence

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

/-- The literal coboundary of one actual upper physical basis word. -/
noncomputable def basisSyndrome (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (q : FamilyQ S depth i.succ) : (indexedFamily S depth).Cochain2 i.succ :=
  (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord (F := BDL26Field) q)

theorem basisSyndrome_valid (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (q : FamilyQ S depth i.succ) :
    basisSyndrome S depth i q ∈ (indexedFamily S depth).syndromeSubmodule i.succ :=
  ⟨canonicalBasisWord q, rfl⟩

/-- Validity follows from an actual error preimage, with no agreement premise. -/
noncomputable def sigmaPlus (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    (indexedFamily S depth).Syndrome i.succ :=
  ⟨sigma.val + basisSyndrome S depth i q, by
    obtain ⟨e, he⟩ := sigma.property
    refine ⟨e + canonicalBasisWord q, ?_⟩
    change (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
      sigma.val + (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord q)
    rw [map_add, he]⟩

theorem sigmaPlus_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    (sigmaPlus S depth i sigma q).val = sigma.val + basisSyndrome S depth i q := rfl

theorem input_difference (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    sigma.val + (sigmaPlus S depth i sigma q).val = basisSyndrome S depth i q := by
  funext p
  change sigma.val p + (sigma.val p + basisSyndrome S depth i q p) = _
  rw [← add_assoc, ZModModule.add_self, zero_add]

theorem sigmaPlus_preimage (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    ∃ e : (indexedFamily S depth).Cochain1 i.succ,
      (indexedFamily S depth).coboundary1 i.succ e = sigma.val ∧
      (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
        (sigmaPlus S depth i sigma q).val := by
  obtain ⟨e, he⟩ := sigma.property
  refine ⟨e, he, ?_⟩
  change (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
    sigma.val + (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord q)
  rw [map_add, he]

/-- U(z): the finite union of the actual radius-two source syndrome regions. -/
noncomputable def readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (z : FamilyZ S depth i.castSucc) : Finset (FamilyZ S depth i.succ) :=
  (xiIndexSet (rxData S depth i h).levelGraph.graph ((rxData S depth i h).coarseCenter z) 2).biUnion
    (fun v => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v)

theorem mem_readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (z : FamilyZ S depth i.castSucc) (p : FamilyZ S depth i.succ) :
    p ∈ readRegion S depth i h z ↔
      ∃ v ∈ xiIndexSet (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).coarseCenter z) 2,
        p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v :=
  Finset.mem_biUnion

/-- J(q) is computed from the actual upper basis coboundary and U(z). -/
noncomputable def influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) : Finset (FamilyZ S depth i.castSucc) :=
  Finset.univ.filter fun z =>
    ((hammingSupport (basisSyndrome S depth i q)) ∩ readRegion S depth i h z).Nonempty

theorem mem_influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc) :
    z ∈ influence S depth i h q ↔
      ∃ p, basisSyndrome S depth i q p ≠ 0 ∧ p ∈ readRegion S depth i h z := by
  simp only [influence, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Membership in the intersection retains the actual upper support.
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2,
      (Finset.mem_inter.mp hp).2⟩
  · rintro ⟨p, hp, hregion⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, hregion⟩⟩

theorem basisSyndrome_zero_on_readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : basisSyndrome S depth i q p = 0 := by
  by_contra hp0
  exact hz ((mem_influence S depth i h q z).mpr ⟨p, hp0, hp⟩)

theorem input_agreement (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : sigma.val p = (sigmaPlus S depth i sigma q).val p := by
  change sigma.val p = sigma.val p + basisSyndrome S depth i q p
  rw [basisSyndrome_zero_on_readRegion S depth i h q z hz p hp, add_zero]

/-- Derive equality of the finite actual xi sums from each contributing region. -/
theorem aggregate_agreement (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) :
    rxXiSignal (rxData S depth i h) sigma.val ((rxData S depth i h).coarseCenter z) 2 =
      rxXiSignal (rxData S depth i h) (sigmaPlus S depth i sigma q).val
        ((rxData S depth i h).coarseCenter z) 2 := by
  funext p
  change Finset.sum
    (xiIndexSet (rxData S depth i h).levelGraph.graph ((rxData S depth i h).coarseCenter z) 2)
    (fun v => maskWord ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v) sigma.val p) =
    Finset.sum
      (xiIndexSet (rxData S depth i h).levelGraph.graph ((rxData S depth i h).coarseCenter z) 2)
      (fun v => maskWord ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v)
        (sigmaPlus S depth i sigma q).val p)
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v
  · simp only [maskWord, if_pos hp]
    exact input_agreement S depth i h sigma q z hz p
      ((mem_readRegion S depth i h z p).mpr ⟨v, hv, hp⟩)
  · simp only [maskWord, if_neg hp]

/-- Canonical selected-run coarse output, without replacing the decoder. -/
theorem canonical_coarse (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).coarse.val = rxCoarseWord (rxData S depth i h) sigma.val :=
  rxStepOutput_coarse S depth i h sigma

theorem coarse_eq_outside_influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (_hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val z := by
  rw [canonical_coarse, canonical_coarse]
  exact (rx_coarse_word_invariant_at_center (rxData S depth i h) sigma.val z).trans
    ((congrArg (fun word => rxCoarseWord (rxData S depth i h) word z)
      (aggregate_agreement S depth i h sigma q z hz)).trans
        (rx_coarse_word_invariant_at_center (rxData S depth i h)
          (sigmaPlus S depth i sigma q).val z).symm)

/-- Full lower syndrome difference support; no parent-fibre support is asserted. -/
theorem coarse_difference_support (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val) ⊆
        influence S depth i h q := by
  intro z hz
  by_contra hnot
  have heq := coarse_eq_outside_influence S depth i h hi sigma q z hnot
  have hz0 : (rxStepOutput S depth i h sigma).coarse.val z +
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val z ≠ 0 :=
    (Finset.mem_filter.mp hz).2
  apply hz0
  rw [← heq]
  exact ZModModule.add_self _

end QEC.Coding.BDL26RXCoarseInfluence
