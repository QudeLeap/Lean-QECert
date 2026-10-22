import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Snapshots
import Mathlib.Order.Interval.Finset.Nat

/-! # Finite interval propagation through the actual C2 suffix -/
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

variable (S : OddScale) (n : Nat)

abbrev Coordinates (a : LevelIndex n) :=
  FamilyZ S (n+2) (LevelTwoHistory.physicalLevel a)

/-- Number of actual RX steps on the half-open physical interval. -/
def rxCount (a b : Nat) : Nat :=
  ((Finset.Ico a b).filter (fun k => k % 2 = 0)).card

theorem rxCount_self (a : Nat) : rxCount a a = 0 := by simp [rxCount]

theorem rxCount_succ (a b : Nat) (hab : a ≤ b) :
    rxCount a (b+1) = rxCount a b + if b % 2 = 0 then 1 else 0 := by
  by_cases h : b % 2 = 0
  · have he : ((Finset.Ico a (b+1)).filter (fun k => k % 2 = 0)) =
        insert b ((Finset.Ico a b).filter (fun k => k % 2 = 0)) := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_Ico,Finset.mem_insert]
      omega
    have hn : b ∉ (Finset.Ico a b).filter (fun k => k % 2 = 0) := by
      intro hm
      exact (Nat.lt_irrefl b) (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).2
    simpa only [rxCount,if_pos h] using
      (congrArg Finset.card he).trans (Finset.card_insert_of_notMem hn)
  · have he : ((Finset.Ico a (b+1)).filter (fun k => k % 2 = 0)) =
        (Finset.Ico a b).filter (fun k => k % 2 = 0) := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_Ico]
      omega
    simpa only [rxCount,if_neg h,Nat.add_zero] using congrArg Finset.card he

theorem rxCount_formula (a b : Nat) (hab : a ≤ b) :
    rxCount a b = (b+1)/2 - (a+1)/2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp [rxCount]
  | succ k ih =>
      rw [show a+(k+1) = (a+k)+1 by omega, rxCount_succ _ _ (by omega), ih (by omega)]
      by_cases h : (a+k) % 2 = 0
      · rw [if_pos h]
        omega
      · rw [if_neg h]
        omega

/-- The interval set only composes the original physical-step dependence maps. -/
def propagate (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    Finset (Coordinates S n a) := by
  cases b with
  | zero =>
      exact (show (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
        Fin.ext (by change 0 = a.val; omega)) ▸ A
  | succ b =>
      if h : a.val = b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
          Fin.ext h.symm) ▸ A
      else
        exact propagate b (by omega) a (by omega)
          (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A)
termination_by b

theorem propagate_self (b : Nat) (hb : b ≤ n)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    propagate S n b hb ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) A = A := by
  cases b with
  | zero => rw [propagate] <;> rfl
  | succ b =>
      rw [propagate]
      exact dif_pos rfl

theorem propagate_succ (b : Nat) (hb : b+1 ≤ n) (a : LevelIndex n)
    (ha : a.val ≤ b) (A : Finset (Coordinates S n ⟨b+1,Nat.lt_succ_of_le hb⟩)) :
    propagate S n (b+1) hb a (by omega) A =
      propagate S n b (by omega) a ha
        (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A) := by
  have hne : ¬ a.val = b+1 := by omega
  rw [propagate]
  exact dif_neg hne

theorem propagate_mono (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    {A B : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)} (hab : A ⊆ B) :
    propagate S n b hb a ha A ⊆ propagate S n b hb a ha B := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simpa only [propagate_self] using hab
  | succ b ih =>
      by_cases he : a.val = b+1
      · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        simpa only [propagate_self] using hab
      · rw [propagate_succ S n b hb a (by omega), propagate_succ S n b hb a (by omega)]
        exact ih _ _ _ (stepPropagation_mono S (n+2) _ hab)

theorem physical_stepFactor (b : Nat) (hb : b < n) :
    stepFactor (n+2) (LevelTwoHistory.physicalStep (⟨b,hb⟩ : StepIndex n)) =
      if b % 2 = 0 then 57 else 1 := by
  change (if (b+2) % 2 = 0 then 57 else 1) = if b % 2 = 0 then 57 else 1
  have hp : (b+2) % 2 = b % 2 := by omega
  exact congrArg (fun r : Nat => if r = 0 then 57 else 1) hp

theorem propagate_card (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    (propagate S n b hb a ha A).card ≤ 57 ^ rxCount a.val b * A.card := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simp only [propagate_self, rxCount_self, pow_zero, one_mul, le_refl]
  | succ b ih =>
      by_cases he : a.val = b+1
      · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        simp only [propagate_self, rxCount_self, pow_zero, one_mul, le_refl]
      · have ha' : a.val ≤ b := by omega
        rw [propagate_succ S n b hb a ha']
        have hr := ih (by omega) a ha'
          (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A)
        have hs := stepPropagation_card S (n+2)
          (LevelTwoHistory.physicalStep (⟨b,by omega⟩ : StepIndex n)) A
        rw [physical_stepFactor n b (by omega)] at hs
        have hc := hr.trans (Nat.mul_le_mul_left _ hs)
        rw [rxCount_succ _ _ ha']
        by_cases hp : b % 2 = 0
        · simpa only [if_pos hp, pow_succ, Nat.mul_assoc] using hc
        · simpa only [if_neg hp, Nat.add_zero, one_mul] using hc

theorem prefix_pair_support (b : Nat) (hb : b ≤ n)
    (sigma tau : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    hammingSupport
      ((prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
          b hb sigma a ha).val +
        (prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
          b hb tau a ha).val) ⊆
      propagate S n b hb a ha (hammingSupport (sigma.val + tau.val)) := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simpa only [prefixInput_self, propagate_self] using
        (show hammingSupport (sigma.val + tau.val) ⊆ hammingSupport (sigma.val + tau.val)
          from fun _ h => h)
  | succ b ih =>
      by_cases he : a.val = b+1
      · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        simpa only [prefixInput_self, propagate_self] using
          (show hammingSupport (sigma.val + tau.val) ⊆ hammingSupport (sigma.val + tau.val)
            from fun _ h => h)
      · have ha' : a.val ≤ b := by omega
        rw [prefixInput_succ _ _ b hb sigma a ha', prefixInput_succ _ _ b hb tau a ha',
          propagate_succ S n b hb a ha']
        have hr := ih (by omega)
          ((actualStep S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)) sigma).coarse
          ((actualStep S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)) tau).coarse a ha'
        exact hr.trans (propagate_mono S n b (by omega) a ha'
          (step_pair_support S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) sigma tau))

theorem actualInputs_interval (sigma : TopInput S n) (b a : LevelIndex n)
    (ha : a.val ≤ b.val) :
    actualInputs S n sigma a =
      prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a ha :=
  prefixInput_comp (SuffixData S n)
    (LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2)) (actualAboveTwoSteps S n))
    n (Nat.le_refl _) sigma b a (Nat.le_of_lt_succ b.isLt) ha

theorem propagate_comp (c : Nat) (hc : c ≤ n)
    (A : Finset (Coordinates S n ⟨c,Nat.lt_succ_of_le hc⟩))
    (b a : LevelIndex n) (hb : b.val ≤ c) (ha : a.val ≤ b.val) :
    propagate S n c hc a (ha.trans hb) A =
      propagate S n b.val (Nat.le_of_lt_succ b.isLt) a ha
        (propagate S n c hc b hb A) := by
  induction c generalizing b a with
  | zero =>
      have hb0 : b = ⟨0,Nat.lt_succ_of_le hc⟩ := Fin.ext (by change b.val = 0; omega)
      have ha0 : a = ⟨0,Nat.lt_succ_of_le hc⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      subst b
      simp only [propagate_self]
  | succ c ih =>
      by_cases he : b.val = c+1
      · have heb : b = ⟨c+1,Nat.lt_succ_of_le hc⟩ := Fin.ext he
        subst b
        rw [propagate_self]
      · have hbc : b.val ≤ c := by omega
        rw [propagate_succ S n c hc a (ha.trans hbc),
          propagate_succ S n c hc b hbc]
        exact ih (by omega) _ b a hbc ha

theorem rxCount_comp (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    rxCount a c = rxCount a b + rxCount b c := by
  rw [rxCount_formula _ _ (hab.trans hbc), rxCount_formula _ _ hab,
    rxCount_formula _ _ hbc]
  omega

theorem actual_interval_support (sigma tau : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    hammingSupport (actualReadout S n sigma a + actualReadout S n tau a) ⊆
      propagate S n b.val (Nat.le_of_lt_succ b.isLt) a ha
        (hammingSupport (actualReadout S n sigma b + actualReadout S n tau b)) := by
  rw [actualInputs_readout, actualInputs_readout, actualInputs_readout, actualInputs_readout]
  rw [actualInputs_interval S n sigma b a ha, actualInputs_interval S n tau b a ha]
  exact prefix_pair_support S n b.val (Nat.le_of_lt_succ b.isLt) _ _ a ha

theorem actual_interval_weight (sigma tau : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n tau a) ≤
      57 ^ ((b.val+1)/2 - (a.val+1)/2) *
        HammingWeight (actualReadout S n sigma b + actualReadout S n tau b) := by
  have hs := Finset.card_le_card (actual_interval_support S n sigma tau a b ha)
  have hc := propagate_card S n b.val (Nat.le_of_lt_succ b.isLt) a ha
    (hammingSupport (actualReadout S n sigma b + actualReadout S n tau b))
  rw [rxCount_formula _ _ ha] at hc
  exact hs.trans hc

end QEC.Coding.BDL26HistorySyndromeSensitivity
