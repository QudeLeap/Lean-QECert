import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Snapshots
import QEC.Coding.FiniteAlternatingConstruction.RXErrorPullback
import QEC.Coding.FiniteAlternatingConstruction.RZErrorPullback

/-! # Internally constructed actual error representatives

Every descent keeps the selected correction and the full upper delta0
potential. Validity of the top input constructs the initial preimage; no
lower preimage or compatibility certificate is supplied to the endpoint.
-/
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

def errorInput (S : OddScale) (d : Nat) (i : StepIndex d)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Syndrome i.succ :=
  ⟨(indexedFamily S d).coboundary1 i.succ e,⟨e,rfl⟩⟩

theorem actual_pullback (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) :
    ∃ (l : (indexedFamily S d).Cochain1 i.castSucc)
      (p : (indexedFamily S d).Cochain0 i.succ),
      ((indexedDecoderData S d).selectedMap i).map1 l =
        e + (actualStep S d i (errorInput S d i e)).correction +
          (indexedFamily S d).coboundary0 i.succ p ∧
      (indexedFamily S d).coboundary1 i.castSucc l =
        (actualStep S d i (errorInput S d i e)).coarse.val ∧
      (indexedFamily S d).coboundary1 i.succ
        ((indexedFamily S d).coboundary0 i.succ p) = 0 := by
  by_cases h : i.val % 2 = 0
  · obtain ⟨l,p,hl,hd,_,hp⟩ := BDL26RXErrorPullback.one_run S d i hi h e
    have hr : BDL26RXErrorPullback.run S d i h e = actualStep S d i (errorInput S d i e) := by
      rw [BDL26RXErrorPullback.run, actualStep_rx S d i h]
      rfl
    exact ⟨l,p,by simpa only [hr] using hl,by simpa only [hr] using hd,hp⟩
  · obtain ⟨l,p,hl,hd,_,hp⟩ := BDL26RZErrorPullback.one_run S d i hi h e
    have hr : BDL26RZErrorPullback.run S d i h e = actualStep S d i (errorInput S d i e) := by
      rw [BDL26RZErrorPullback.run, actualStep_rz S d i h]
      rfl
    exact ⟨l,p,by simpa only [hr] using hl,by simpa only [hr] using hd,hp⟩

def lowerRepresentative (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Cochain1 i.castSucc :=
  Classical.choose (actual_pullback S d i hi e)

def fullPotential (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Cochain0 i.succ :=
  Classical.choose (Classical.choose_spec (actual_pullback S d i hi e))

theorem lowerRepresentative_spec (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) :
    ((indexedDecoderData S d).selectedMap i).map1 (lowerRepresentative S d i hi e) =
      e + (actualStep S d i (errorInput S d i e)).correction +
        (indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e) ∧
    (indexedFamily S d).coboundary1 i.castSucc (lowerRepresentative S d i hi e) =
      (actualStep S d i (errorInput S d i e)).coarse.val ∧
    (indexedFamily S d).coboundary1 i.succ
      ((indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e)) = 0 :=
  Classical.choose_spec (Classical.choose_spec (actual_pullback S d i hi e))

variable (S : OddScale) (n : Nat)

/-- The same upper word, with its original physical-step carrier explicit. -/
def physicalUpperError (i : StepIndex n)
    (e : (SuffixData S n).family.Cochain1 i.succ) :
    (indexedFamily S (n+2)).Cochain1 (LevelTwoHistory.physicalStep i).succ := e

theorem physicalUpperError_eq (i : StepIndex n)
    (e : (SuffixData S n).family.Cochain1 i.succ) :
    physicalUpperError S n i e = e := rfl

def errorDown (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) : (SuffixData S n).family.Cochain1 a := by
  cases b with
  | zero =>
      exact (show (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
        Fin.ext (by change 0 = a.val; omega)) ▸ e
  | succ b =>
      if h : a.val = b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
          Fin.ext h.symm) ▸ e
      else
        exact errorDown b (by omega)
          (lowerRepresentative S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (by simp only [LevelTwoHistory.physicalStep_val]; omega) e) a (by omega)
termination_by b

theorem errorDown_self (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩) :
    errorDown S n b hb e ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) = e := by
  cases b with
  | zero => rw [errorDown] <;> rfl
  | succ b =>
      rw [errorDown]
      exact dif_pos rfl

theorem errorDown_succ (b : Nat) (hb : b+1 ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b+1,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    errorDown S n (b+1) hb e a (by omega) =
      errorDown S n b (by omega)
        (lowerRepresentative S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
          (by simp only [LevelTwoHistory.physicalStep_val]; omega) e) a ha := by
  have hne : ¬ a.val = b+1 := by omega
  rw [errorDown]
  exact dif_neg hne

theorem errorDown_valid (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩)
    (sigma : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (he : (SuffixData S n).family.coboundary1 _ e = sigma.val)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    (SuffixData S n).family.coboundary1 a (errorDown S n b hb e a ha) =
      (prefixInput (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b hb sigma a ha).val := by
  induction b generalizing a with
  | zero =>
      have ha0 : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simpa only [errorDown_self, prefixInput_self] using he
  | succ b ih =>
      by_cases ha' : a.val = b+1
      · have hae : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext ha'
        subst a
        simpa only [errorDown_self, prefixInput_self] using he
      · have hal : a.val ≤ b := by omega
        let k : StepIndex (n+2) := LevelTwoHistory.physicalStep (⟨b,by omega⟩ : StepIndex n)
        have hk : 2 ≤ k.val := by simp only [k,LevelTwoHistory.physicalStep_val]; omega
        have hs : errorInput S (n+2) k e = sigma := Subtype.ext he
        have hd := (lowerRepresentative_spec S (n+2) k hk e).2.1
        rw [hs] at hd
        rw [errorDown_succ S n b hb e a hal, prefixInput_succ _ _ b hb sigma a hal]
        exact ih (by omega) _ (actualStep S (n+2) k sigma).coarse hd a hal

theorem errorDown_step (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩)
    (i : StepIndex n) (hi : i.val < b) :
    errorDown S n b hb e i.castSucc (by change i.val ≤ b; omega) =
      lowerRepresentative S (n+2) (LevelTwoHistory.physicalStep i)
        (by simp only [LevelTwoHistory.physicalStep_val]; omega)
        (errorDown S n b hb e i.succ (by change i.val+1 ≤ b; omega)) := by
  induction b generalizing i with
  | zero => omega
  | succ b ih =>
      by_cases he : i.val = b
      · have hbn : b < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb
        have hei : i = ⟨b,hbn⟩ := Fin.ext he
        subst i
        let k : StepIndex (n+2) := LevelTwoHistory.physicalStep (⟨b,by omega⟩ : StepIndex n)
        have hk : 2 ≤ k.val := by change 2 ≤ b+2; omega
        let l := lowerRepresentative S (n+2) k hk e
        have hl := errorDown_succ S n b hb e
          (⟨b,by omega⟩ : StepIndex n).castSucc (Nat.le_refl _)
        have hs := errorDown_self S n b (by omega) l
        have hu := errorDown_self S n (b+1) hb e
        exact hl.trans (hs.trans (congrArg (lowerRepresentative S (n+2) k hk) hu.symm))
      · have hil : i.val+1 ≤ b := by omega
        rw [errorDown_succ S n b hb e i.castSucc (by change i.val ≤ b; omega),
          errorDown_succ S n b hb e i.succ (by change i.val+1 ≤ b; omega)]
        exact ih (by omega) _ i (by omega)

/-- The complete representative/potential chain is constructed from top validity. -/
theorem actual_preimage_chain (sigma : TopInput S n) :
    ∃ (E : ∀ a : LevelIndex n, (SuffixData S n).family.Cochain1 a)
      (P : ∀ i : StepIndex n,
        (indexedFamily S (n+2)).Cochain0 (LevelTwoHistory.physicalStep i).succ),
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) (E (TopIndex n)) = sigma.val ∧
      (∀ a, (SuffixData S n).family.coboundary1 a (E a) = actualReadout S n sigma a) ∧
      (∀ i, ((indexedDecoderData S (n+2)).selectedMap (LevelTwoHistory.physicalStep i)).map1
        (E i.castSucc) = physicalUpperError S n i (E i.succ) +
          (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
            (actualInputs S n sigma i.succ)).correction +
          (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalStep i).succ (P i)) ∧
      (∀ i, (indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalStep i).succ
        ((indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalStep i).succ (P i)) = 0) := by
  obtain ⟨e,he⟩ := sigma.property
  let E : ∀ a : LevelIndex n, (SuffixData S n).family.Cochain1 a := fun a =>
    errorDown S n n (Nat.le_refl _) e a (Nat.le_of_lt_succ a.isLt)
  let P := fun i : StepIndex n => fullPotential S (n+2) (LevelTwoHistory.physicalStep i)
    (by simp only [LevelTwoHistory.physicalStep_val]; omega) (E i.succ)
  have hv (a : LevelIndex n) : (SuffixData S n).family.coboundary1 a (E a) =
      (actualInputs S n sigma a).val :=
    errorDown_valid S n n (Nat.le_refl _) e sigma he a (Nat.le_of_lt_succ a.isLt)
  refine ⟨E,P,?_,?_,?_,?_⟩
  · have htop := errorDown_self S n n (Nat.le_refl _) e
    exact (congrArg ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) htop).trans he
  · intro a
    rw [actualInputs_readout]
    exact hv a
  · intro i
    have hstep : E i.castSucc = lowerRepresentative S (n+2) (LevelTwoHistory.physicalStep i)
        (by simp only [LevelTwoHistory.physicalStep_val]; omega) (E i.succ) :=
      errorDown_step S n n (Nat.le_refl _) e i i.isLt
    have hinput : errorInput S (n+2) (LevelTwoHistory.physicalStep i) (E i.succ) =
        actualInputs S n sigma i.succ := Subtype.ext (hv i.succ)
    rw [hstep]
    have hs := (lowerRepresentative_spec S (n+2) (LevelTwoHistory.physicalStep i)
      (by simp only [LevelTwoHistory.physicalStep_val]; omega) (E i.succ)).1
    rw [hinput] at hs
    exact hs
  · intro i
    exact (lowerRepresentative_spec S (n+2) (LevelTwoHistory.physicalStep i)
      (by simp only [LevelTwoHistory.physicalStep_val]; omega) (E i.succ)).2.2

end QEC.Coding.BDL26HistorySyndromeSensitivity
