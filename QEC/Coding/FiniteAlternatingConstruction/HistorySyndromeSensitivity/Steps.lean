import QEC.Coding.FiniteAlternatingConstruction.RXInfluenceBounds
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.History

/-! # Actual one-step syndrome sensitivity

Arbitrary valid backgrounds are compared through the actual radius-two RX
readers and the disjoint RZ parity blocks. No correction selector is assumed
linear, and the sets below carry no parent or component interpretation.
-/
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem binary_add_eq_zero_iff (a b : BDL26Field) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = (a + b) + b := by rw [add_assoc, ZModModule.add_self, add_zero]
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact ZModModule.add_self _

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

def rxPropagation (h : i.val % 2 = 0) (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) :=
  A.biUnion (readers S depth i h)

theorem rxPropagation_card (h : i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) :
    (rxPropagation S depth i h A).card ≤ 57 * A.card := by
  exact (Finset.card_biUnion_le_card_mul A (readers S depth i h) 57
    (fun p _ => readers_card_le S depth i h p)).trans_eq (Nat.mul_comm _ _)

theorem rx_coarse_agreement (h : i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ)
    (z : FamilyZ S depth i.castSucc)
    (ha : ∀ p ∈ readRegion S depth i h z, sigma.val p = tau.val p) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h tau).coarse.val z := by
  have hag : rxXiSignal (rxData S depth i h) sigma.val
      ((rxData S depth i h).coarseCenter z) 2 =
      rxXiSignal (rxData S depth i h) tau.val
        ((rxData S depth i h).coarseCenter z) 2 := by
    funext p
    change Finset.sum _ (fun v => maskWord
      ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v) sigma.val p) =
      Finset.sum _ (fun v => maskWord
        ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v) tau.val p)
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v
    · simp only [maskWord, if_pos hp]
      exact ha p ((mem_readRegion S depth i h z p).mpr ⟨v,hv,hp⟩)
    · simp only [maskWord, if_neg hp]
  rw [canonical_coarse, canonical_coarse]
  exact (rx_coarse_word_invariant_at_center (rxData S depth i h) sigma.val z).trans
    ((congrArg (fun w => rxCoarseWord (rxData S depth i h) w z) hag).trans
      (rx_coarse_word_invariant_at_center (rxData S depth i h) tau.val z).symm)

theorem rx_pair_support (h : i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h tau).coarse.val) ⊆
      rxPropagation S depth i h (hammingSupport (sigma.val + tau.val)) := by
  intro z hz
  by_contra hn
  have he : (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h tau).coarse.val z := by
    apply rx_coarse_agreement S depth i h sigma tau z
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hsum
    apply hn
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsum⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  exact (Finset.mem_filter.mp hz).2 ((binary_add_eq_zero_iff _ _).mpr he)

/-- The owner is derived from the actual disjoint covering blocks. -/
def rzBlockOwner (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ) :
    FamilyZ S depth i.castSucc :=
  Classical.choose ((rzData S depth i h).coarseRegion_cover p)

theorem rzBlockOwner_mem (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ) :
    p ∈ (rzData S depth i h).coarseRegion (rzBlockOwner S depth i h p) :=
  Classical.choose_spec ((rzData S depth i h).coarseRegion_cover p)

theorem rzBlockOwner_eq (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ)
    (z : FamilyZ S depth i.castSucc) (hp : p ∈ (rzData S depth i h).coarseRegion z) :
    rzBlockOwner S depth i h p = z := by
  by_contra hn
  exact Finset.disjoint_left.mp ((rzData S depth i h).coarseRegion_disjoint _ _ hn)
    (rzBlockOwner_mem S depth i h p) hp

def rzPropagation (h : ¬ i.val % 2 = 0) (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) := A.image (rzBlockOwner S depth i h)

theorem mem_rzPropagation (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) (z : FamilyZ S depth i.castSucc) :
    z ∈ rzPropagation S depth i h A ↔
      ∃ p ∈ A, p ∈ (rzData S depth i h).coarseRegion z := by
  constructor
  · intro hz
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz
    exact ⟨p,hp,he ▸ rzBlockOwner_mem S depth i h p⟩
  · rintro ⟨p,hp,hz⟩
    exact Finset.mem_image.mpr ⟨p,hp,rzBlockOwner_eq S depth i h p z hz⟩

theorem rzPropagation_card (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) :
    (rzPropagation S depth i h A).card ≤ A.card := Finset.card_image_le

theorem rz_pair_support (h : ¬ i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((rzStepOutput S depth i h sigma).coarse.val +
      (rzStepOutput S depth i h tau).coarse.val) ⊆
      rzPropagation S depth i h (hammingSupport (sigma.val + tau.val)) := by
  intro z hz
  by_contra hn
  have hag : ∀ p ∈ (rzData S depth i h).coarseRegion z, sigma.val p = tau.val p := by
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hsum
    apply hn
    exact (mem_rzPropagation S depth i h _ z).mpr
      ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsum⟩,hp⟩
  have he : (rzStepOutput S depth i h sigma).coarse.val z =
      (rzStepOutput S depth i h tau).coarse.val z := by
    rw [rzStepOutput_coarse_apply, rzStepOutput_coarse_apply]
    exact Finset.sum_congr rfl hag
  exact (Finset.mem_filter.mp hz).2 ((binary_add_eq_zero_iff _ _).mpr he)

def stepPropagation (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) :=
  if h : i.val % 2 = 0 then rxPropagation S depth i h A else rzPropagation S depth i h A

def stepFactor : Nat := if i.val % 2 = 0 then 57 else 1

theorem stepPropagation_mono
    {A B : Finset (FamilyZ S depth i.succ)} (hab : A ⊆ B) :
    stepPropagation S depth i A ⊆ stepPropagation S depth i B := by
  by_cases h : i.val % 2 = 0
  · simp only [stepPropagation, dif_pos h, rxPropagation]
    intro z hz
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨p,hab hp,hz⟩
  · simp only [stepPropagation, dif_neg h, rzPropagation]
    exact Finset.image_subset_image hab

theorem stepPropagation_card (A : Finset (FamilyZ S depth i.succ)) :
    (stepPropagation S depth i A).card ≤ stepFactor depth i * A.card := by
  by_cases h : i.val % 2 = 0
  · simpa only [stepPropagation, stepFactor, dif_pos h, if_pos h] using
      rxPropagation_card S depth i h A
  · simpa only [stepPropagation, stepFactor, dif_neg h, if_neg h, one_mul] using
      rzPropagation_card S depth i h A

theorem step_pair_support (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((actualStep S depth i sigma).coarse.val +
      (actualStep S depth i tau).coarse.val) ⊆
      stepPropagation S depth i (hammingSupport (sigma.val + tau.val)) := by
  by_cases h : i.val % 2 = 0
  · rw [congrFun (actualStep_rx S depth i h) sigma,
      congrFun (actualStep_rx S depth i h) tau]
    simpa only [stepPropagation, dif_pos h] using rx_pair_support S depth i h sigma tau
  · rw [congrFun (actualStep_rz S depth i h) sigma,
      congrFun (actualStep_rz S depth i h) tau]
    simpa only [stepPropagation, dif_neg h] using rz_pair_support S depth i h sigma tau

end QEC.Coding.BDL26HistorySyndromeSensitivity
