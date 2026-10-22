import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Steps
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.Snapshots

/-! # A proof traversal of the literal stored history

The finite-prefix equations expose the existing assembly recursion. Uniqueness
of that finite recursion identifies it with buildCorrectionHistory, so readouts
below always refer to that original history, including its actual base input.
-/
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

universe u
section Prefix
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

/-- Public proof equations for the unchanged finite assembly prefix. -/
def prefixHistory (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat)
    (hn : n ≤ depth) (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    CorrectionHistory D := by
  cases n with
  | zero =>
      exact [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }]
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n,hstep⟩
      have hi : i.succ = ⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n,Nat.lt_succ_of_le hnext⟩ := Fin.ext rfl
      exact .step i out :: prefixHistory D S B n hnext (hcoarse ▸ out.coarse)
termination_by n

/-- The proof prefix is the original assembly algorithm, not a replacement. -/
theorem prefixHistory_top_eq (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    prefixHistory D S B depth (Nat.le_refl _) sigma = buildCorrectionHistory D S B sigma := by
  symm
  apply buildCorrectionHistory_eq_of_recursion D S B (prefixHistory D S B)
  · intro hn s
    rw [prefixHistory] <;> rfl
  · intro n hn s
    rw [prefixHistory] <;> rfl

/-- Read the actually selected input at any level of a finite prefix. -/
def prefixInput (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) : D.family.Syndrome a := by
  cases n with
  | zero =>
      have he : (⟨0,Nat.lt_succ_of_le hn⟩ : LevelIndex depth) = a :=
        Fin.ext (by change 0 = a.val; omega)
      exact he ▸ sigma
  | succ n =>
      if h : a.val = n+1 then
        exact (show (⟨n+1,Nat.lt_succ_of_le hn⟩ : LevelIndex depth) = a from
          Fin.ext h.symm) ▸ sigma
      else
        have hs : n < depth := by omega
        exact prefixInput D S n (by omega) (S.step ⟨n,hs⟩ sigma).coarse a (by omega)
termination_by n

theorem prefixInput_self (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    prefixInput D S n hn sigma ⟨n,Nat.lt_succ_of_le hn⟩ (Nat.le_refl _) = sigma := by
  cases n with
  | zero => rw [prefixInput] <;> rfl
  | succ n =>
      rw [prefixInput]
      exact dif_pos rfl

theorem prefixInput_succ (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n+1 ≤ depth)
    (sigma : D.family.Syndrome ⟨n+1,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) :
    prefixInput D S (n+1) hn sigma a (by omega) =
      prefixInput D S n (by omega) (S.step ⟨n,by omega⟩ sigma).coarse a ha := by
  have hne : ¬ a.val = n+1 := by omega
  rw [prefixInput]
  exact dif_neg hne

theorem prefixHistory_level_le (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    ∀ e ∈ prefixHistory D S B n hn sigma, e.inputSyndrome.1.val ≤ n := by
  induction n with
  | zero =>
      intro e he
      rw [prefixHistory] at he
      have he' : e = .base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm } := List.mem_singleton.mp he
      subst e
      exact Nat.le_refl 0
  | succ n ih =>
      intro e he
      rw [prefixHistory] at he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact Nat.le_refl _
      · exact (ih _ _ e he).trans (Nat.le_succ n)

theorem historyReadout_cons (D : BDL26DecoderData depth C0 C1 C2)
    (e : CorrectionHistoryEntry D) (H : CorrectionHistory D) (a : LevelIndex depth) :
    historyInputReadout D (e :: H) a =
      (if h : e.inputSyndrome.1 = a then h ▸ e.inputSyndrome.2.val else 0) +
        historyInputReadout D H a := by
  simp only [historyInputReadout, List.map_cons, List.sum_cons]

theorem historyReadout_step_same (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D) :
    historyInputReadout D (.step i out :: H) i.succ =
      out.input.val + historyInputReadout D H i.succ := by
  rw [historyReadout_cons]
  change (if h : i.succ = i.succ then h ▸ out.input.val else 0) + _ = _
  rw [dif_pos rfl]

theorem historyReadout_step_ne (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D)
    (a : LevelIndex depth) (ha : i.succ ≠ a) :
    historyInputReadout D (.step i out :: H) a = historyInputReadout D H a := by
  rw [historyReadout_cons]
  change (if h : i.succ = a then h ▸ out.input.val else 0) + _ = _
  split_ifs with h
  · exact False.elim (ha h)
  · exact zero_add _

theorem prefixReadout_above (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : n < a.val) :
    historyInputReadout D (prefixHistory D S B n hn sigma) a = 0 := by
  unfold historyInputReadout
  apply List.sum_eq_zero
  intro w hw
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hw
  have hne : e.inputSyndrome.1 ≠ a := by
    intro heq
    have hb := prefixHistory_level_le D S B n hn sigma e he
    rw [heq] at hb
    omega
  simp only [dif_neg hne]

/-- The recursively computed input is precisely the original stored readout. -/
theorem prefixInput_readout (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) :
    historyInputReadout D (prefixHistory D S B n hn sigma) a =
      (prefixInput D S n hn sigma a ha).val := by
  induction n generalizing a with
  | zero =>
      have he : a = 0 := Fin.ext (by change a.val = 0; omega)
      subst a
      let b : RecursiveBaseLevelCorrection D := {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }
      have hh : prefixHistory D S B 0 hn sigma = [.base b] := by
        rw [prefixHistory]
        rfl
      have hr := congrArg (fun H : CorrectionHistory D => historyInputReadout D H 0) hh
      exact hr.trans ((historyInputReadout_base D b).trans
        (congrArg Subtype.val (prefixInput_self D S 0 hn sigma)).symm)
  | succ n ih =>
      by_cases he : a.val = n+1
      · have hea : a = ⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext he
        subst a
        let i : StepIndex depth := ⟨n,by omega⟩
        let out := S.step i sigma
        let tail := prefixHistory D S B n (by omega) out.coarse
        have hh : prefixHistory D S B (n+1) hn sigma = .step i out :: tail := by
          rw [prefixHistory]
        have hr := (congrArg (fun H : CorrectionHistory D =>
          historyInputReadout D H i.succ) hh).trans (historyReadout_step_same D i out tail)
        have ht := prefixReadout_above D S B n (by omega)
          out.coarse i.succ (by change n < n+1; omega)
        exact hr.trans ((congrArg (fun w => out.input.val + w) ht).trans
          ((add_zero _).trans
            ((congrArg Subtype.val ((S.relation i).input_eq sigma)).trans
              (congrArg Subtype.val (prefixInput_self D S (n+1) hn sigma)).symm)))
      · have hal : a.val ≤ n := by omega
        rw [prefixInput_succ D S n hn sigma a hal, prefixHistory]
        have hne : (⟨n,by omega⟩ : StepIndex depth).succ ≠ a := by
          intro h
          exact he (congrArg Fin.val h).symm
        exact (historyReadout_step_ne D _ _ _ a hne).trans (ih _ _ a hal)

theorem prefixInput_comp (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (b a : LevelIndex depth) (hb : b.val ≤ n) (ha : a.val ≤ b.val) :
    prefixInput D S n hn sigma a (ha.trans hb) =
      prefixInput D S b.val (by omega) (prefixInput D S n hn sigma b hb) a ha := by
  induction n generalizing b a with
  | zero =>
      have hb0 : b.val = 0 := by omega
      have ha0 : a.val = 0 := by omega
      cases a with | mk av hav =>
        cases b with | mk bv hbv =>
          simp only [Fin.val_mk] at hb0 ha0
          subst av
          subst bv
          simp only [prefixInput_self]
  | succ n ih =>
      by_cases he : b.val = n+1
      · have heb : b = ⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext he
        subst b
        rw [prefixInput_self]
      · have hbn : b.val ≤ n := by omega
        rw [prefixInput_succ D S n hn sigma a (ha.trans hbn),
          prefixInput_succ D S n hn sigma b hbn]
        exact ih _ _ b a hbn ha
end Prefix

variable (S : OddScale) (n : Nat)
abbrev SuffixData := LevelTwoHistory.suffixData (indexedDecoderData S (n+2))
abbrev TopInput := (indexedFamily S (n+2)).Syndrome (TopIndex (n+2))

def actualInputs (sigma : TopInput S n) (a : LevelIndex n) :
    (SuffixData S n).family.Syndrome a :=
  prefixInput (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) n (Nat.le_refl _) sigma a
      (Nat.le_of_lt_succ a.isLt)

def actualReadout (sigma : TopInput S n) (a : LevelIndex n) :=
  LevelTwoHistory.syndromeReadout (indexedDecoderData S (n+2))
    (actualHistory S n sigma) (LevelTwoHistory.physicalLevel a)

theorem actualInputs_readout (sigma : TopInput S n) (a : LevelIndex n) :
    actualReadout S n sigma a = (actualInputs S n sigma a).val := by
  let st := LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2)) (actualAboveTwoSteps S n)
  let s : (SuffixData S n).family.Syndrome (TopIndex n) := sigma
  have he := prefixHistory_top_eq (SuffixData S n) st (actualBase S n) s
  have hr := prefixInput_readout (SuffixData S n) st (actualBase S n) n
    (Nat.le_refl _) s a (Nat.le_of_lt_succ a.isLt)
  have hp := LevelTwoHistory.syndromeReadout_physical (indexedDecoderData S (n+2))
    (actualHistory S n sigma) a
  exact hp.trans ((congrArg (fun H : CorrectionHistory (SuffixData S n) =>
    historyInputReadout (SuffixData S n) H a) he).symm.trans hr)

theorem actualInputs_top (sigma : TopInput S n) :
    actualInputs S n sigma (TopIndex n) = sigma :=
  prefixInput_self _ _ _ _ _

/-- Consecutive inputs are exactly the real selector's coarse output. -/
theorem actualInputs_step (sigma : TopInput S n) (i : StepIndex n) :
    actualInputs S n sigma i.castSucc =
      (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
        (actualInputs S n sigma i.succ)).coarse := by
  have h := prefixInput_comp (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) n (Nat.le_refl _) sigma
    i.succ i.castSucc (by have := i.isLt; omega) (by simp)
  change actualInputs S n sigma i.castSucc =
    prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
      (i.val+1) (by have := i.isLt; omega) (actualInputs S n sigma i.succ)
      i.castSucc (by simp) at h
  have hd := prefixInput_succ (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) i.val
    (by have := i.isLt; omega) (actualInputs S n sigma i.succ) i.castSucc (Nat.le_refl _)
  have hs := prefixInput_self (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) i.val
    (Nat.le_of_lt i.isLt)
    (actualStep S (n+2) (LevelTwoHistory.physicalStep i) (actualInputs S n sigma i.succ)).coarse
  exact h.trans (hd.trans hs)

end QEC.Coding.BDL26HistorySyndromeSensitivity
