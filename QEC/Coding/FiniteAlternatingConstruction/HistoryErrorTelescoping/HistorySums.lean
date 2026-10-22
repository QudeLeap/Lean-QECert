import QEC.Coding.FiniteAlternatingConstruction.HistoryErrorTelescoping.Intervals

/-! # Position-preserving sums of the original stopped history

The eligibility tests inspect only original levels. In particular a zero word,
a repeated word and a nonzero cycle are retained at their original positions.
The interval sum excludes the base; the assembled prefix always retains it.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical

universe u v

section Lists
variable {A : Type u} {W : Type v} [AddCommMonoid W]

theorem sum_filterMap_eq_sum_getD (f : A → Option W) (L : List A) :
    (L.filterMap f).sum = (L.map (fun a => (f a).getD 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      cases h : f a with
      | none => simp [h,ih]
      | some w => simp [h,ih]

end Lists

section OriginalLists
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

/-- Lift an original eligible entry; the real base entry is always eligible. -/
def prefixEntry (D : BDL26DecoderData depth C0 C1 C2)
    (b : LevelIndex depth) : CorrectionHistoryEntry D → Option (D.family.Cochain1 b)
  | .base B => some (intervalMap1 D 0 b (Nat.zero_le _) B.correction)
  | .step i O => if h : i.succ.val ≤ b.val then
      some (intervalMap1 D i.succ b h O.correction) else none

/-- Retain exactly the original nonbase positions in the half-open interval. -/
def intervalEntry (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) : CorrectionHistoryEntry D → Option (D.family.Cochain1 b)
  | .base _ => none
  | .step i O => if h : a.val < i.succ.val ∧ i.succ.val ≤ b.val then
      some (intervalMap1 D i.succ b h.2 O.correction) else none

def historyPrefixSum (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) : D.family.Cochain1 b :=
  (H.filterMap (prefixEntry D b)).sum

def historyIntervalSum (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth) : D.family.Cochain1 b :=
  (H.filterMap (intervalEntry D a b)).sum

theorem historyPrefixSum_cons (D : BDL26DecoderData depth C0 C1 C2)
    (e : CorrectionHistoryEntry D) (H : CorrectionHistory D) (b : LevelIndex depth) :
    historyPrefixSum D (e :: H) b = (prefixEntry D b e).getD 0 + historyPrefixSum D H b := by
  simp only [historyPrefixSum,sum_filterMap_eq_sum_getD,List.map_cons,List.sum_cons]

theorem prefixEntry_split (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) (hab : a.val ≤ b.val) (e : CorrectionHistoryEntry D) :
    (prefixEntry D b e).getD 0 = (intervalEntry D a b e).getD 0 +
      intervalMap1 D a b hab ((prefixEntry D a e).getD 0) := by
  cases e with
  | base B =>
      simp only [prefixEntry,intervalEntry,Option.getD_some,Option.getD_none,zero_add]
      exact congrArg (fun f => f B.correction)
        (intervalMap1_comp D 0 a b (Nat.zero_le _) hab)
  | step i O =>
      by_cases hia : i.succ.val ≤ a.val
      · have hib : i.succ.val ≤ b.val := hia.trans hab
        have hno : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by omega
        simp only [prefixEntry,intervalEntry,dif_pos hia,dif_pos hib,dif_neg hno,
          Option.getD_some,Option.getD_none,zero_add]
        exact congrArg (fun f => f O.correction) (intervalMap1_comp D i.succ a b hia hab)
      · by_cases hib : i.succ.val ≤ b.val
        · have hyes : a.val < i.succ.val ∧ i.succ.val ≤ b.val := ⟨by omega,hib⟩
          simp only [prefixEntry,intervalEntry,dif_neg hia,dif_pos hib,dif_pos hyes,
            Option.getD_some,Option.getD_none,map_zero,add_zero]
        · have hno : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by omega
          simp only [prefixEntry,intervalEntry,dif_neg hia,dif_neg hib,dif_neg hno,
            Option.getD_none,map_zero,add_zero]

/-- Every lower prefix term, including the base, survives in the decomposition. -/
theorem historyPrefixSum_split (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth) (hab : a.val ≤ b.val) :
    historyPrefixSum D H b = historyIntervalSum D H a b +
      intervalMap1 D a b hab (historyPrefixSum D H a) := by
  simp only [historyPrefixSum,historyIntervalSum,sum_filterMap_eq_sum_getD]
  induction H with
  | nil => simp
  | cons e H ih =>
      simp only [List.map_cons,List.sum_cons,map_add]
      rw [prefixEntry_split D a b hab e,ih]
      ac_rfl

theorem historyIntervalSum_self (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a : LevelIndex depth) : historyIntervalSum D H a a = 0 := by
  have hnone : ∀ e : CorrectionHistoryEntry D, intervalEntry D a a e = none := by
    intro e
    cases e with
    | base B => rfl
    | step i O =>
        have h : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ a.val) := by omega
        exact dif_neg h
  induction H with
  | nil => rfl
  | cons e H ih =>
      change ((e :: H).filterMap (intervalEntry D a a)).sum = 0
      rw [List.filterMap_cons,hnone e]
      exact ih

theorem intervalEntry_split (D : BDL26DecoderData depth C0 C1 C2)
    (a b c : LevelIndex depth) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val)
    (e : CorrectionHistoryEntry D) :
    (intervalEntry D a c e).getD 0 =
      intervalMap1 D b c hbc ((intervalEntry D a b e).getD 0) +
        (intervalEntry D b c e).getD 0 := by
  cases e with
  | base B => simp [intervalEntry]
  | step i O =>
      by_cases hai : a.val < i.succ.val
      · by_cases hib : i.succ.val ≤ b.val
        · have hic := hib.trans hbc
          have hac : a.val < i.succ.val ∧ i.succ.val ≤ c.val := ⟨hai,hic⟩
          have hab' : a.val < i.succ.val ∧ i.succ.val ≤ b.val := ⟨hai,hib⟩
          have hbc' : ¬ (b.val < i.succ.val ∧ i.succ.val ≤ c.val) := by omega
          simp only [intervalEntry,dif_pos hac,dif_pos hab',dif_neg hbc',
            Option.getD_some,Option.getD_none,add_zero]
          exact congrArg (fun f => f O.correction) (intervalMap1_comp D i.succ b c hib hbc)
        · by_cases hic : i.succ.val ≤ c.val
          · have hac : a.val < i.succ.val ∧ i.succ.val ≤ c.val := ⟨hai,hic⟩
            have hab' : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by omega
            have hbc' : b.val < i.succ.val ∧ i.succ.val ≤ c.val := ⟨by omega,hic⟩
            simp only [intervalEntry,dif_pos hac,dif_neg hab',dif_pos hbc',
              Option.getD_some,Option.getD_none,map_zero,zero_add]
          · have hac : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ c.val) := by omega
            have hab' : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by omega
            have hbc' : ¬ (b.val < i.succ.val ∧ i.succ.val ≤ c.val) := by omega
            simp only [intervalEntry,dif_neg hac,dif_neg hab',dif_neg hbc',
              Option.getD_none,map_zero,add_zero]
      · have hac : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ c.val) := by omega
        have hab' : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by omega
        have hbc' : ¬ (b.val < i.succ.val ∧ i.succ.val ≤ c.val) := by omega
        simp only [intervalEntry,dif_neg hac,dif_neg hab',dif_neg hbc',
          Option.getD_none,map_zero,add_zero]

theorem historyIntervalSum_comp (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b c : LevelIndex depth)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    historyIntervalSum D H a c =
      intervalMap1 D b c hbc (historyIntervalSum D H a b) + historyIntervalSum D H b c := by
  simp only [historyIntervalSum,sum_filterMap_eq_sum_getD]
  induction H with
  | nil => simp
  | cons e H ih =>
      simp only [List.map_cons,List.sum_cons,map_add]
      rw [intervalEntry_split D a b c hab hbc e,ih]
      ac_rfl

theorem historyPrefixSum_top (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) :
    historyPrefixSum D H (TopIndex depth) = historyLiftedCorrection D H := by
  rw [historyPrefixSum,sum_filterMap_eq_sum_getD]
  unfold historyLiftedCorrection
  congr 1
  apply List.map_congr_left
  intro e he
  cases e with
  | base B =>
      simp only [prefixEntry,Option.getD_some,CorrectionHistoryEntry.correction]
      exact intervalMap1_top D 0 B.correction
  | step i O =>
      have hi : i.succ.val ≤ (TopIndex depth).val := Nat.le_of_lt_succ i.succ.isLt
      simp only [prefixEntry,dif_pos hi,Option.getD_some,CorrectionHistoryEntry.correction]
      exact intervalMap1_top D i.succ O.correction

def historyThrough (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) : CorrectionHistory D :=
  H.filter (fun e => decide (e.level ≤ b.val))

theorem historyThrough_levels (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) :
    ∀ e ∈ historyThrough D H b, e.level ≤ b.val := by
  intro e he
  have h := (List.mem_filter.mp he).2
  exact of_decide_eq_true h

theorem historyThrough_all (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth)
    (h : ∀ e ∈ H, e.level ≤ b.val) : historyThrough D H b = H := by
  induction H with
  | nil => rfl
  | cons e H ih =>
      have he := h e (by simp)
      have ht : ∀ e ∈ H, e.level ≤ b.val := fun e he => h e (by simp [he])
      simpa [historyThrough,he] using congrArg (List.cons e) (ih ht)

theorem prefixEntry_none_of_above (D : BDL26DecoderData depth C0 C1 C2)
    (b : LevelIndex depth) (e : CorrectionHistoryEntry D) (h : ¬ e.level ≤ b.val) :
    prefixEntry D b e = none := by
  cases e with
  | base B => exact False.elim (h (Nat.zero_le _))
  | step i O => exact dif_neg h

theorem historyPrefixSum_through (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) :
    historyPrefixSum D (historyThrough D H b) b = historyPrefixSum D H b := by
  induction H with
  | nil => rfl
  | cons e H ih =>
      by_cases he : e.level ≤ b.val
      · have ht : historyThrough D (e :: H) b = e :: historyThrough D H b := by
          simp [historyThrough,he]
        rw [ht,historyPrefixSum_cons,historyPrefixSum_cons,ih]
      · have hn := prefixEntry_none_of_above D b e he
        have ht : historyThrough D (e :: H) b = historyThrough D H b := by
          simp [historyThrough,he]
        rw [ht,historyPrefixSum_cons,hn,Option.getD_none,zero_add]
        exact ih

theorem historyIntervalSum_zero_of_levels (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth)
    (h : ∀ e ∈ H, e.level ≤ a.val) : historyIntervalSum D H a b = 0 := by
  rw [historyIntervalSum,sum_filterMap_eq_sum_getD]
  apply List.sum_eq_zero
  intro w hw
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hw
  cases e with
  | base B => rfl
  | step i O =>
      have hi := h (.step i O) he
      have hn : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ b.val) := by
        change i.succ.val ≤ a.val at hi
        omega
      simp only [intervalEntry,dif_neg hn,Option.getD_none]

theorem historyPrefixSum_lift (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth) (hab : a.val ≤ b.val)
    (h : ∀ e ∈ H, e.level ≤ a.val) :
    historyPrefixSum D H b = intervalMap1 D a b hab (historyPrefixSum D H a) := by
  have hs := historyPrefixSum_split D H a b hab
  rw [historyIntervalSum_zero_of_levels D H a b h,zero_add] at hs
  exact hs

/-- Filtering the original recursion keeps precisely its same-provider prefix. -/
theorem prefixHistory_through (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (m : Nat) (hm : m ≤ depth)
    (s : D.family.Syndrome ⟨m,Nat.lt_succ_of_le hm⟩)
    (b : LevelIndex depth) (hb : b.val ≤ m) :
    historyThrough D (prefixHistory D st B m hm s) b =
      prefixHistory D st B b.val (hb.trans hm) (prefixInput D st m hm s b hb) := by
  induction m generalizing b with
  | zero =>
      have he : b = ⟨0,Nat.lt_succ_of_le hm⟩ := Fin.ext (by change b.val = 0; omega)
      subst b
      rw [prefixInput_self]
      apply historyThrough_all
      intro e he
      have h := prefixHistory_level_le D st B 0 hm s e he
      cases e <;> exact h
  | succ m ih =>
      by_cases he : b.val = m+1
      · have heb : b = ⟨m+1,Nat.lt_succ_of_le hm⟩ := Fin.ext he
        subst b
        rw [prefixInput_self]
        apply historyThrough_all
        intro e he
        have h := prefixHistory_level_le D st B (m+1) hm s e he
        cases e <;> exact h
      · have hbm : b.val ≤ m := by omega
        let i : StepIndex depth := ⟨m,Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm⟩
        let out := st.step i s
        have hh : prefixHistory D st B (m+1) hm s =
            .step i out :: prefixHistory D st B m (by omega) out.coarse := by
          rw [prefixHistory]
        rw [prefixInput_succ D st m hm s b hbm,hh]
        have hn : ¬ (CorrectionHistoryEntry.step i out).level ≤ b.val := by
          change ¬ m+1 ≤ b.val
          omega
        simpa [historyThrough,hn] using ih (by omega) out.coarse b hbm

/-- Closed equations reduce the actual recursion's dependent Nat cases once. -/
theorem prefixHistory_zero_eq (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D) (s : D.family.Syndrome 0) :
    prefixHistory D st B 0 (Nat.zero_le _) s =
      [.base {
        input := s
        correction := B.decode s
        relation := (B.rightInverse s).symm }] := by
  have hz (hn : 0 ≤ depth)
      (t : D.family.Syndrome ⟨0,Nat.lt_succ_of_le hn⟩) :
      prefixHistory D st B 0 hn t = [.base {
        input := t
        correction := B.decode t
        relation := (B.rightInverse t).symm }] := by
    rw [prefixHistory] <;> rfl
  exact hz (Nat.zero_le _) s

theorem prefixHistory_step_eq (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (i : StepIndex depth) (s : D.family.Syndrome i.succ) :
    prefixHistory D st B (i.val+1) (Nat.succ_le_of_lt i.isLt) s =
      .step i (st.step i s) ::
        prefixHistory D st B i.val (Nat.le_of_lt i.isLt) (st.step i s).coarse := by
  rw [prefixHistory] <;> rfl

end OriginalLists

section ActualHistory
variable (S : OddScale) (n : Nat)

theorem actual_intervalMap0_adjacent (i : StepIndex n) :
    intervalMap0 (SuffixData S n) i.castSucc i.succ (by simp) =
      BDL26AlternatingCochain.nextMap0 S (i.val+2) (state S (i.val+2)) := by
  rw [intervalMap0_adjacent,LevelTwoHistory.suffix_selected_map0,selectedMap_eq]
  rfl

theorem actual_intervalMap1_adjacent (i : StepIndex n) :
    intervalMap1 (SuffixData S n) i.castSucc i.succ (by simp) =
      BDL26AlternatingCochain.nextMap1 S (i.val+2) (state S (i.val+2)) := by
  rw [intervalMap1_adjacent,LevelTwoHistory.suffix_selected_map1,selectedMap_eq]
  rfl

/-- The literal selected output at the original stored suffix input. -/
def actualOutput (sigma : TopInput S n) (i : StepIndex n) :
    AssemblyStepOutput (SuffixData S n) i :=
  (LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2))
    (actualAboveTwoSteps S n)).step i (actualInputs S n sigma i.succ)

theorem actualOutput_correction (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).correction =
      (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
        (actualInputs S n sigma i.succ)).correction := rfl

theorem actualOutput_coarse (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).coarse = actualInputs S n sigma i.castSucc :=
  (actualInputs_step S n sigma i).symm

def correctionIntervalSum (sigma : TopInput S n) (a b : LevelIndex n) :
    (SuffixData S n).family.Cochain1 b :=
  historyIntervalSum (SuffixData S n) (actualHistory S n sigma) a b

def assembledPrefix (sigma : TopInput S n) (b : LevelIndex n) :
    (SuffixData S n).family.Cochain1 b :=
  historyPrefixSum (SuffixData S n) (actualHistory S n sigma) b

theorem assembledPrefix_split (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    assembledPrefix S n sigma b = correctionIntervalSum S n sigma a b +
      intervalMap1 (SuffixData S n) a b hab (assembledPrefix S n sigma a) :=
  historyPrefixSum_split _ _ a b hab

theorem correctionIntervalSum_self (sigma : TopInput S n) (a : LevelIndex n) :
    correctionIntervalSum S n sigma a a = 0 := historyIntervalSum_self _ _ a

theorem correctionIntervalSum_comp (sigma : TopInput S n) (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    correctionIntervalSum S n sigma a c =
      intervalMap1 (SuffixData S n) b c hbc (correctionIntervalSum S n sigma a b) +
        correctionIntervalSum S n sigma b c :=
  historyIntervalSum_comp _ _ a b c hab hbc

theorem assembledPrefix_top (sigma : TopInput S n) :
    assembledPrefix S n sigma (TopIndex n) =
      historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) :=
  historyPrefixSum_top _ _

theorem assembledPrefix_globalCorrection (sigma : TopInput S n) :
    assembledPrefix S n sigma (TopIndex n) =
      globalCorrection (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma := by
  rw [assembledPrefix_top]
  exact historyLiftedCorrection_eq_globalCorrection _ _ _ _

theorem actualHistory_through (sigma : TopInput S n) (b : LevelIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) b =
      prefixHistory (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) := by
  change historyThrough (SuffixData S n) (buildCorrectionHistory _ _ _ sigma) b = _
  have hh := prefixHistory_top_eq (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma
  rw [← hh]
  exact prefixHistory_through (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    n (Nat.le_refl _) sigma b (Nat.le_of_lt_succ b.isLt)

theorem assembledPrefix_zero (sigma : TopInput S n) :
    assembledPrefix S n sigma 0 = (actualBase S n).decode (actualInputs S n sigma 0) := by
  change historyPrefixSum (SuffixData S n) (actualHistory S n sigma) 0 = _
  rw [← historyPrefixSum_through,actualHistory_through]
  change historyPrefixSum (SuffixData S n)
    (prefixHistory (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
      0 (Nat.zero_le _) (actualInputs S n sigma 0)) 0 = _
  rw [prefixHistory_zero_eq (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    (actualInputs S n sigma 0)]
  simp only [historyPrefixSum,List.filterMap_cons,List.filterMap_nil,prefixEntry,
    List.sum_cons,List.sum_nil,add_zero,intervalMap1_self,LinearMap.id_apply]

theorem actualHistory_through_succ (sigma : TopInput S n) (i : StepIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) i.succ =
      .step i (actualOutput S n sigma i) ::
        historyThrough (SuffixData S n) (actualHistory S n sigma) i.castSucc := by
  rw [actualHistory_through,actualHistory_through]
  have hs := actualOutput_coarse S n sigma i
  rw [← hs]
  change prefixHistory (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    (i.val+1) (by have := i.isLt; omega) (actualInputs S n sigma i.succ) = _
  rw [prefixHistory_step_eq] <;> rfl

theorem assembledPrefix_succ (sigma : TopInput S n) (i : StepIndex n) :
    assembledPrefix S n sigma i.succ = (actualOutput S n sigma i).correction +
      ((SuffixData S n).selectedMap i).map1 (assembledPrefix S n sigma i.castSucc) := by
  let D := SuffixData S n
  let H := actualHistory S n sigma
  change historyPrefixSum D H i.succ = _
  calc
    historyPrefixSum D H i.succ = historyPrefixSum D (historyThrough D H i.succ) i.succ :=
      (historyPrefixSum_through D H i.succ).symm
    _ = (actualOutput S n sigma i).correction +
        historyPrefixSum D (historyThrough D H i.castSucc) i.succ := by
      rw [actualHistory_through_succ,historyPrefixSum_cons]
      simp only [prefixEntry,dif_pos (Nat.le_refl _),Option.getD_some,
        intervalMap1_self,LinearMap.id_apply] <;> rfl
    _ = (actualOutput S n sigma i).correction +
        (D.selectedMap i).map1 (historyPrefixSum D H i.castSucc) := by
      rw [historyPrefixSum_lift D _ i.castSucc i.succ (by simp)
        (historyThrough_levels D H i.castSucc),intervalMap1_adjacent,historyPrefixSum_through]

theorem correctionIntervalSum_adjacent (sigma : TopInput S n) (i : StepIndex n) :
    correctionIntervalSum S n sigma i.castSucc i.succ = (actualOutput S n sigma i).correction := by
  have hs := assembledPrefix_split S n sigma i.castSucc i.succ (by simp)
  rw [intervalMap1_adjacent] at hs
  exact add_right_cancel (hs.symm.trans (assembledPrefix_succ S n sigma i))

theorem correctionIntervalSum_succ (sigma : TopInput S n)
    (a : LevelIndex n) (i : StepIndex n) (hai : a.val ≤ i.val) :
    correctionIntervalSum S n sigma a i.succ =
      ((SuffixData S n).selectedMap i).map1 (correctionIntervalSum S n sigma a i.castSucc) +
        (actualOutput S n sigma i).correction := by
  rw [correctionIntervalSum_comp S n sigma a i.castSucc i.succ hai (by simp),
    intervalMap1_adjacent,correctionIntervalSum_adjacent]

/-- A finite ordered list of actual stored step snapshots in the interval.
It is a proved alternative presentation of the original-list sum, not its
definition. Every snapshot is retained regardless of its correction value. -/
def snapshotWords (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    List ((SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩) := by
  cases b with
  | zero => exact []
  | succ b =>
      if h : a.val = b+1 then exact []
      else
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        exact (actualOutput S n sigma i).correction ::
          (snapshotWords sigma a b (by omega) (by omega)).map ((SuffixData S n).selectedMap i).map1
termination_by b

theorem snapshotWords_zero_eq (sigma : TopInput S n) (a : LevelIndex n)
    (ha : a.val ≤ 0) : snapshotWords S n sigma a 0 (Nat.zero_le _) ha = [] := by
  rw [snapshotWords] <;> rfl

theorem snapshotWords_succ_eq (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b+1 ≤ n) (ha : a.val ≤ b+1) :
    snapshotWords S n sigma a (b+1) hb ha =
      if h : a.val = b+1 then [] else
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        (actualOutput S n sigma i).correction ::
          (snapshotWords S n sigma a b (by omega) (by omega)).map
            ((SuffixData S n).selectedMap i).map1 := by
  rw [snapshotWords] <;> rfl

theorem linearMap_list_sum {W : Type u} {Z : Type v}
    [AddCommMonoid W] [Module BDL26Field W] [AddCommMonoid Z] [Module BDL26Field Z]
    (f : W →ₗ[BDL26Field] Z) (L : List W) : (L.map f).sum = f L.sum := by
  induction L with
  | nil => simp only [List.map_nil,List.sum_nil,map_zero]
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih,map_add]

theorem snapshotWords_sum (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    (snapshotWords S n sigma a b hb ha).sum =
      correctionIntervalSum S n sigma a ⟨b,Nat.lt_succ_of_le hb⟩ := by
  induction b with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      rw [correctionIntervalSum_self,snapshotWords_zero_eq] <;> rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        rw [correctionIntervalSum_self,snapshotWords_succ_eq,dif_pos he,List.sum_nil]
      · have hal : a.val ≤ b := by omega
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        rw [snapshotWords_succ_eq,dif_neg he]
        change ((actualOutput S n sigma i).correction ::
          (snapshotWords S n sigma a b (by omega) hal).map ((SuffixData S n).selectedMap i).map1).sum =
          correctionIntervalSum S n sigma a i.succ
        have ht := ih (by omega) hal
        change (snapshotWords S n sigma a b (by omega) hal).sum =
          correctionIntervalSum S n sigma a i.castSucc at ht
        rw [List.sum_cons,linearMap_list_sum,ht,
          correctionIntervalSum_succ S n sigma a i hal]
        exact add_comm _ _

theorem snapshotWords_length (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    (snapshotWords S n sigma a b hb ha).length = b-a.val := by
  induction b with
  | zero => rw [snapshotWords_zero_eq]; simp
  | succ b ih =>
      by_cases he : a.val = b+1
      · rw [snapshotWords_succ_eq,dif_pos he]
        simp only [List.length_nil,he,Nat.sub_self]
      · rw [snapshotWords_succ_eq,dif_neg he]
        simp only [List.length_cons,List.length_map,ih (by omega) (by omega)]
        omega

theorem snapshotWords_components (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).correction = (actualOutput S n sigma i).localComponents.sum :=
  (actualOutput S n sigma i).correction_decomposition

theorem lifted_actual_components (sigma : TopInput S n) (i : StepIndex n)
    (b : LevelIndex n) (hib : i.succ.val ≤ b.val) :
    intervalMap1 (SuffixData S n) i.succ b hib (actualOutput S n sigma i).correction =
      ((actualOutput S n sigma i).localComponents.map
        (intervalMap1 (SuffixData S n) i.succ b hib)).sum := by
  rw [snapshotWords_components]
  exact (linearMap_list_sum _ _).symm

theorem actualCorrection_split (sigma : TopInput S n) :
    historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) =
      correctionIntervalSum S n sigma 0 (TopIndex n) +
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          ((actualBase S n).decode (actualInputs S n sigma 0)) := by
  rw [← assembledPrefix_top,assembledPrefix_split S n sigma 0 (TopIndex n) (Nat.zero_le _),
    assembledPrefix_zero]

end ActualHistory
end QEC.Coding.BDL26HistoryErrorTelescoping
