import QEC.Coding.FiniteAlternatingConstruction.PairedHistoryQueryCone.ReadBounds
import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity
import QEC.Coding.FiniteAlternatingConstruction.HistoryErrorTelescoping.HistorySums

/-!
# Paired active queries of the actual selected history

The forward sets depend only on the physical flip. Backward queries retain
every potentially affected selector block, together with the stopping-level
coordinates needed to reproduce coalescence. At C2 the seed is the entire
genuine bottom input. This permits a global bottom decoder without assigning
it a fictitious local read region.
-/
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators

abbrev TopWord (S : OddScale) (n : Nat) :=
  (SuffixData S n).family.Cochain1 (TopIndex n)

variable (S : OddScale) (n : Nat)

/-- A background-independent potential support, used for both paired runs. -/
def potential (e : TopWord S n) (a : LevelIndex n) : Finset (Coordinates S n a) :=
  propagate S n n (Nat.le_refl _) a (Nat.le_of_lt_succ a.isLt)
    (hammingSupport ((SuffixData S n).family.coboundary1 (TopIndex n) e))

theorem potential_support (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n) :
    hammingSupport ((actualInputs S n s a).val +
      (actualInputs S n (perturbTop S n s e) a).val) ⊆ potential S n e a := by
  have ht : s.val + (perturbTop S n s e).val =
      (SuffixData S n).family.coboundary1 (TopIndex n) e := by
    change s.val + (s.val + _) = _
    rw [← add_assoc,binary_word_add_self,zero_add]
    change ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) e =
      ((indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalLevel (TopIndex n))) e
    rw [indexedFamily_coboundary1]
  have hs := prefix_pair_support S n n (Nat.le_refl _) s (perturbTop S n s e)
    a (Nat.le_of_lt_succ a.isLt)
  rw [ht] at hs
  exact hs

theorem potential_card (e : TopWord S n) (a : LevelIndex n) :
    (potential S n e a).card ≤ 57 ^ (n-a.val) *
      HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) := by
  have hc := propagate_card S n n (Nat.le_refl _) a (Nat.le_of_lt_succ a.isLt)
    (hammingSupport ((SuffixData S n).family.coboundary1 (TopIndex n) e))
  have hr : rxCount a.val n ≤ n-a.val := by
    rw [rxCount_formula _ _ (Nat.le_of_lt_succ a.isLt)]
    omega
  exact hc.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hr))

/-- Only a genuine C2 endpoint has a full-input seed. A positive stopping
level retains U, rather than discarding the queries that certify its zero. -/
def querySeed (e : TopWord S n) (a : LevelIndex n) : Finset (Coordinates S n a) :=
  if a.val = 0 then Finset.univ else potential S n e a

def queryPrefix (e : TopWord S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩) := by
  cases b with
  | zero =>
      if h : a.val = 0 then
        exact (show a = ⟨0,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else exact ∅
  | succ b =>
      if h : a.val = b+1 then
        exact (show a = ⟨b+1,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else if ha : a.val ≤ b then
        exact correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
          (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩) ∪
          liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (queryPrefix e a b (by omega))
      else exact ∅
termination_by b

private theorem queryPrefix_zero_eq (e : TopWord S n) (a : LevelIndex n) (hb : 0 ≤ n) :
    queryPrefix S n e a 0 hb =
      if h : a.val = 0 then
        (show a = ⟨0,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else ∅ := by
  rw [queryPrefix] <;> rfl

private theorem queryPrefix_succ_eq (e : TopWord S n) (a : LevelIndex n)
    (b : Nat) (hb : b+1 ≤ n) :
    queryPrefix S n e a (b+1) hb =
      if h : a.val = b+1 then
        (show a = ⟨b+1,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else if ha : a.val ≤ b then
        correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
          (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩) ∪
          liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (queryPrefix S n e a b (by omega))
      else ∅ := by
  rw [queryPrefix] <;> rfl

def queries (e : TopWord S n) (a b : LevelIndex n) : Finset (Coordinates S n b) :=
  queryPrefix S n e a b.val (Nat.le_of_lt_succ b.isLt)

theorem queries_self (e : TopWord S n) (a : LevelIndex n) :
    queries S n e a a = querySeed S n e a := by
  rcases a with ⟨a,ha⟩
  cases a with
  | zero => rw [queries,queryPrefix]; exact dif_pos rfl
  | succ a => rw [queries,queryPrefix]; exact dif_pos rfl

theorem queries_below (e : TopWord S n) (a b : LevelIndex n) (h : b.val < a.val) :
    queries S n e a b = ∅ := by
  rcases b with ⟨b,hb⟩
  cases b with
  | zero =>
      change 0 < a.val at h
      change queryPrefix S n e a 0 _ = ∅
      rw [queryPrefix_zero_eq]
      exact dif_neg (by omega)
  | succ b =>
      change b+1 < a.val at h
      change queryPrefix S n e a (b+1) _ = ∅
      rw [queryPrefix_succ_eq,dif_neg (by omega),dif_neg (by omega)]

theorem queries_step (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) :
    queries S n e a i.succ =
      correctionQueries S (n+2) (LevelTwoHistory.physicalStep i) (potential S n e i.succ) ∪
        liftQueries S (n+2) (LevelTwoHistory.physicalStep i) (queries S n e a i.castSucc) := by
  rcases i with ⟨b,hb⟩
  change a.val ≤ b at ha
  change queryPrefix S n e a (b+1) _ =
    correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,hb⟩)
      (potential S n e ⟨b+1,by omega⟩) ∪
      liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,hb⟩) (queryPrefix S n e a b _)
  rw [queryPrefix_succ_eq,dif_neg (by omega),dif_pos ha]

theorem correctionQueries_subset (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) :
    correctionQueries S (n+2) (LevelTwoHistory.physicalStep i) (potential S n e i.succ) ⊆
      queries S n e a i.succ := by
  rw [queries_step S n e a i ha]
  exact Finset.subset_union_left

theorem query_edge_closed (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) (z : Coordinates S n i.castSucc)
    (hz : z ∈ queries S n e a i.castSucc) (p : Coordinates S n i.succ)
    (hp : p ∈ coarseRead S (n+2) (LevelTwoHistory.physicalStep i) z) :
    p ∈ queries S n e a i.succ := by
  rw [queries_step S n e a i ha]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z,hz,hp⟩)

/-- Every query has a finite path from a stopping or affected-selector seed. -/
inductive QueryPath (e : TopWord S n) (a : LevelIndex n) :
    (b : LevelIndex n) → Coordinates S n b → Prop
  | seed (p : Coordinates S n a) (hp : p ∈ querySeed S n e a) : QueryPath e a a p
  | correction (i : StepIndex n) (ha : a.val ≤ i.val) (p : Coordinates S n i.succ)
      (hp : p ∈ correctionQueries S (n+2) (LevelTwoHistory.physicalStep i)
        (potential S n e i.succ)) : QueryPath e a i.succ p
  | lift (i : StepIndex n) (ha : a.val ≤ i.val) (z : Coordinates S n i.castSucc)
      (path : QueryPath e a i.castSucc z) (p : Coordinates S n i.succ)
      (hp : p ∈ coarseRead S (n+2) (LevelTwoHistory.physicalStep i) z) :
      QueryPath e a i.succ p

theorem queryPath_mem (e : TopWord S n) (a : LevelIndex n) {b : LevelIndex n}
    {p : Coordinates S n b} (path : QueryPath S n e a b p) :
    p ∈ queries S n e a b := by
  induction path with
  | seed p hp => simpa only [queries_self] using hp
  | correction i ha p hp => exact correctionQueries_subset S n e a i ha hp
  | lift i ha z path p hp ih => exact query_edge_closed S n e a i ha z ih p hp

theorem mem_queryPath (e : TopWord S n) (a b : LevelIndex n)
    (p : Coordinates S n b) (hp : p ∈ queries S n e a b) : QueryPath S n e a b p := by
  have aux : ∀ b (hb : b ≤ n), ∀ p : Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩,
      p ∈ queries S n e a ⟨b,Nat.lt_succ_of_le hb⟩ →
        QueryPath S n e a ⟨b,Nat.lt_succ_of_le hb⟩ p := by
    intro b
    induction b with
    | zero =>
        intro hb p hp
        by_cases he : a.val = 0
        · have hea : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext he
          subst a
          exact .seed p (by simpa only [queries_self] using hp)
        · have hz := queries_below S n e a ⟨0,Nat.lt_succ_of_le hb⟩
            (by change 0 < a.val; omega)
          simpa only [hz,Finset.notMem_empty] using hp
    | succ b ih =>
        intro hb p hp
        by_cases he : a.val = b+1
        · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
          subst a
          exact .seed p (by simpa only [queries_self] using hp)
        · by_cases ha : a.val ≤ b
          · let i : StepIndex n := ⟨b,by omega⟩
            change p ∈ queries S n e a i.succ at hp
            change QueryPath S n e a i.succ p
            rw [queries_step S n e a i ha] at hp
            rcases Finset.mem_union.mp hp with hp | hp
            · exact .correction i ha p hp
            · obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
              exact .lift i ha z (ih (by omega) z hz) p hp
          · have hz := queries_below S n e a ⟨b+1,Nat.lt_succ_of_le hb⟩
              (by change b+1 < a.val; omega)
            simpa only [hz,Finset.notMem_empty] using hp
  exact aux b.val (Nat.le_of_lt_succ b.isLt) p hp

/-- Top-cylinder agreement replays every query down to the chosen stop. -/
theorem query_agreement (e : TopWord S n) (a : LevelIndex n) (s t : TopInput S n)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (b : LevelIndex n) (hab : a.val ≤ b.val) :
    AgreeOn (queries S n e a b) (actualInputs S n s b).val (actualInputs S n t b).val := by
  have aux : ∀ k, ∀ b : LevelIndex n, n-b.val=k → a.val ≤ b.val →
      AgreeOn (queries S n e a b) (actualInputs S n s b).val (actualInputs S n t b).val := by
    intro k
    induction k with
    | zero =>
        intro b hb hab
        have he : b = TopIndex n := Fin.ext (by have := b.isLt; change b.val = n; omega)
        subst b
        simpa only [actualInputs_top] using htop
    | succ k ih =>
        intro b hb hab
        have hbn : b.val < n := by omega
        let i : StepIndex n := ⟨b.val,hbn⟩
        change AgreeOn (queries S n e a i.castSucc)
          (actualInputs S n s i.castSucc).val (actualInputs S n t i.castSucc).val
        intro z hz
        rw [actualInputs_step,actualInputs_step]
        apply coarse_agreement S (n+2) (LevelTwoHistory.physicalStep i)
        intro p hp
        exact ih i.succ (by dsimp only [i]; simp only [Fin.val_succ]; omega)
          (by change a.val ≤ b.val+1; omega) p
          (query_edge_closed S n e a i hab z hz p hp)
  exact aux (n-b.val) b rfl hab

theorem stopping_replay (e : TopWord S n) (a : LevelIndex n) (ha : 0 < a.val)
    (s t : TopInput S n)
    (hs : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val) :
    actualInputs S n t a = actualInputs S n (perturbTop S n t e) a := by
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ potential S n e a
  · have hm : p ∈ queries S n e a a := by
      rw [queries_self,querySeed,if_neg (by omega)]
      exact hp
    exact (query_agreement S n e a s t htop a (Nat.le_refl _) p hm).symm.trans
      ((congrFun (congrArg Subtype.val hs) p).trans
        (query_agreement S n e a (perturbTop S n s e) (perturbTop S n t e)
          hflip a (Nat.le_refl _) p hm))
  · apply (binary_add_eq_zero_iff _ _).mp
    by_contra hn
    exact hp (potential_support S n t e a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))

theorem paired_step_replay (e : TopWord S n) (a : LevelIndex n) (s t : TopInput S n)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val)
    (i : StepIndex n) (ha : a.val ≤ i.val) :
    (actualOutput S n s i).correction + (actualOutput S n (perturbTop S n s e) i).correction =
      (actualOutput S n t i).correction + (actualOutput S n (perturbTop S n t e) i).correction := by
  apply correction_pair_replay S (n+2) (LevelTwoHistory.physicalStep i)
    (potential S n e i.succ)
  · exact potential_support S n s e i.succ
  · exact potential_support S n t e i.succ
  · exact fun p hp => query_agreement S n e a s t htop i.succ
      (by change a.val ≤ i.val+1; omega) p
      (correctionQueries_subset S n e a i ha hp)
  · exact fun p hp => query_agreement S n e a (perturbTop S n s e)
      (perturbTop S n t e) hflip i.succ (by change a.val ≤ i.val+1; omega) p
        (correctionQueries_subset S n e a i ha hp)

/-- The stopping level is selected from the actual paired stored inputs. -/
def coalescentLevels (s : TopInput S n) (e : TopWord S n) : Finset (LevelIndex n) :=
  Finset.univ.filter fun a => actualInputs S n s a = actualInputs S n (perturbTop S n s e) a

def stoppingLevel (s : TopInput S n) (e : TopWord S n) : LevelIndex n :=
  if h : (coalescentLevels S n s e).Nonempty then (coalescentLevels S n s e).max' h else 0

theorem stoppingLevel_coalesces (s : TopInput S n) (e : TopWord S n)
    (ha : 0 < (stoppingLevel S n s e).val) :
    actualInputs S n s (stoppingLevel S n s e) =
      actualInputs S n (perturbTop S n s e) (stoppingLevel S n s e) := by
  by_cases h : (coalescentLevels S n s e).Nonempty
  · have hs : stoppingLevel S n s e = (coalescentLevels S n s e).max' h := dif_pos h
    rw [hs]
    exact (Finset.mem_filter.mp (Finset.max'_mem _ h)).2
  · have hz : stoppingLevel S n s e = 0 := dif_neg h
    rw [hz] at ha
    change 0 < 0 at ha
    omega

theorem le_stoppingLevel (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n)
    (ha : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a) :
    a ≤ stoppingLevel S n s e := by
  have hm : a ∈ coalescentLevels S n s e := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  rw [stoppingLevel,dif_pos ⟨a,hm⟩]
  exact Finset.le_max' _ a hm

/-- An explicit recursive budget retaining every complete query block. -/
def budgetPrefix (e : TopWord S n) (a : LevelIndex n) (b : Nat) (hb : b ≤ n) : Nat := by
  cases b with
  | zero => exact if a.val = 0 then (querySeed S n e a).card else 0
  | succ b =>
      exact if a.val = b+1 then (querySeed S n e a).card else
        if a.val ≤ b then queryBlockBound S *
          (57 * (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩).card +
            budgetPrefix e a b (by omega)) else 0
termination_by b

private theorem budgetPrefix_zero_eq (e : TopWord S n) (a : LevelIndex n) (hb : 0 ≤ n) :
    budgetPrefix S n e a 0 hb = if a.val = 0 then (querySeed S n e a).card else 0 := by
  rw [budgetPrefix] <;> rfl

private theorem budgetPrefix_succ_eq (e : TopWord S n) (a : LevelIndex n)
    (b : Nat) (hb : b+1 ≤ n) :
    budgetPrefix S n e a (b+1) hb =
      if a.val = b+1 then (querySeed S n e a).card else
        if a.val ≤ b then queryBlockBound S *
          (57 * (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩).card +
            budgetPrefix S n e a b (by omega)) else 0 := by
  rw [budgetPrefix] <;> rfl


theorem queries_card_budget (e : TopWord S n) (a b : LevelIndex n) :
    (queries S n e a b).card ≤ budgetPrefix S n e a b.val (Nat.le_of_lt_succ b.isLt) := by
  have aux : ∀ b (hb : b ≤ n), (queries S n e a ⟨b,Nat.lt_succ_of_le hb⟩).card ≤
      budgetPrefix S n e a b hb := by
    intro b
    induction b with
    | zero =>
        intro hb
        by_cases h : a.val = 0
        · have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext h
          subst a
          simp only [queries_self,budgetPrefix_zero_eq,Fin.val_mk,ite_true,le_refl]
        · have hbelow := queries_below S n e a ⟨0,Nat.lt_succ_of_le hb⟩
            (by change 0 < a.val; omega)
          simp only [hbelow,Finset.card_empty,Nat.zero_le]
    | succ b ih =>
        intro hb
        by_cases h : a.val = b+1
        · have he : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext h
          subst a
          simp only [queries_self,budgetPrefix_succ_eq,Fin.val_mk,ite_true,le_refl]
        · by_cases ha : a.val ≤ b
          · let i : StepIndex n := ⟨b,by omega⟩
            change (queries S n e a i.succ).card ≤ budgetPrefix S n e a (b+1) hb
            rw [queries_step S n e a i ha,budgetPrefix_succ_eq,if_neg h,if_pos ha]
            change (correctionQueries S (n+2) (LevelTwoHistory.physicalStep i)
                (potential S n e i.succ) ∪
              liftQueries S (n+2) (LevelTwoHistory.physicalStep i)
                (queries S n e a i.castSucc)).card ≤
              queryBlockBound S * (57 * (potential S n e i.succ).card +
                budgetPrefix S n e a b (by omega))
            have hu := Finset.card_union_le
              (correctionQueries S (n+2) (LevelTwoHistory.physicalStep i)
                (potential S n e i.succ))
              (liftQueries S (n+2) (LevelTwoHistory.physicalStep i)
                (queries S n e a i.castSucc))
            have hc := correctionQueries_card S (n+2) (LevelTwoHistory.physicalStep i)
              (potential S n e i.succ)
            have hl := liftQueries_card S (n+2) (LevelTwoHistory.physicalStep i)
              (queries S n e a i.castSucc)
            exact hu.trans ((Nat.add_le_add hc
              (hl.trans (Nat.mul_le_mul_left _ (ih (by omega))))).trans_eq (by ring))
          · have hbelow := queries_below S n e a ⟨b+1,Nat.lt_succ_of_le hb⟩
              (by change b+1 < a.val; omega)
            simp only [hbelow,Finset.card_empty,Nat.zero_le]
  exact aux b.val (Nat.le_of_lt_succ b.isLt)

/-- Uniform budget for a finite window. This grows with its length L. -/
def windowBudget (S : OddScale) (L w : Nat) : Nat :=
  (57 * queryBlockBound S + 1) * (57^L*w) * (queryBlockBound S+1)^L

theorem queries_window_card (e : TopWord S n) (a : LevelIndex n) (ha : 0 < a.val)
    (L w : Nat) (hw : HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) ≤ w)
    (hlen : n-a.val ≤ L) :
    (queries S n e a (TopIndex n)).card ≤ windowBudget S L w := by
  let M := 57^L*w
  let C := (57*queryBlockBound S+1)*M
  have hu : ∀ b : LevelIndex n, a.val ≤ b.val → (potential S n e b).card ≤ M := by
    intro b hb
    exact (potential_card S n e b).trans
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) hw)
  have hC : M ≤ C := by dsimp [C]; nlinarith
  have hsource : queryBlockBound S * (57*M) ≤ C := by dsimp [C]; nlinarith
  have aux : ∀ b (hb : b ≤ n), a.val ≤ b →
      (queries S n e a ⟨b,Nat.lt_succ_of_le hb⟩).card ≤
        C*(queryBlockBound S+1)^(b-a.val) := by
    intro b
    induction b with
    | zero => intro hb hab; omega
    | succ b ih =>
        intro hb hab
        by_cases he : a.val = b+1
        · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
          subst a
          rw [queries_self,querySeed,if_neg (by omega),Nat.sub_self,pow_zero,Nat.mul_one]
          exact (hu _ (Nat.le_refl _)).trans hC
        · have hal : a.val ≤ b := by omega
          let i : StepIndex n := ⟨b,by omega⟩
          change (queries S n e a i.succ).card ≤ C*(queryBlockBound S+1)^(b+1-a.val)
          rw [queries_step S n e a i hal]
          have hc := (correctionQueries_card S (n+2) (LevelTwoHistory.physicalStep i)
            (potential S n e i.succ)).trans
              ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 57 (hu i.succ hab))).trans hsource)
          have hl := (liftQueries_card S (n+2) (LevelTwoHistory.physicalStep i)
            (queries S n e a i.castSucc)).trans (Nat.mul_le_mul_left _ (ih (by omega) hal))
          have hp : C ≤ C*(queryBlockBound S+1)^(b-a.val) := by
            exact (Nat.mul_one C).symm.trans_le
              (Nat.mul_le_mul_left C (Nat.one_le_pow _ _ (by omega)))
          have ht := (Finset.card_union_le _ _).trans (Nat.add_le_add hc hl)
          have hex : b+1-a.val = (b-a.val)+1 := by omega
          rw [hex,pow_succ]
          exact ht.trans ((Nat.add_le_add_right hp _).trans_eq (by ring))
  have ht := aux n (Nat.le_refl _) (Nat.le_of_lt_succ a.isLt)
  exact ht.trans (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by omega) hlen))

/-- The actual one-step contraction, with the original physical parity. -/
theorem step_contraction (i : StepIndex n)
    (s : (SuffixData S n).family.Syndrome i.succ) :
    (if i.val % 2 = 0 then 2 else 1) *
      HammingWeight (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse.val ≤
        HammingWeight s.val := by
  by_cases h : i.val % 2 = 0
  · have hp : (LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      change (i.val+2)%2=0
      omega
    rw [if_pos h,actualStep_rx S (n+2) _ hp]
    exact BDL26RXDecoderAdapter.rxStepOutput_weight S (n+2) _ hp s
  · have hp : ¬ (LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      change ¬ (i.val+2)%2=0
      omega
    rw [if_neg h,actualStep_rz S (n+2) _ hp,one_mul]
    exact BDL26RZDecoderAdapter.rzStepOutput_weight S (n+2) _ hp s

theorem prefix_contraction (b : Nat) (hb : b ≤ n)
    (s : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    2 ^ rxCount a.val b * HammingWeight
      (prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
        b hb s a ha).val ≤ HammingWeight s.val := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simp only [rxCount_self,pow_zero,one_mul,prefixInput_self,le_refl]
  | succ b ih =>
      by_cases he : a.val = b+1
      · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        simp only [rxCount_self,pow_zero,one_mul,prefixInput_self,le_refl]
      · have hal : a.val ≤ b := by omega
        let i : StepIndex n := ⟨b,by omega⟩
        rw [prefixInput_succ _ _ b hb s a hal,rxCount_succ _ _ hal]
        have hr := ih (by omega)
          (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse a hal
        have hs := step_contraction S n i s
        by_cases hp : b % 2 = 0
        · rw [if_pos hp,pow_succ]
          have hs' : 2 * HammingWeight
              (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse.val ≤
                HammingWeight s.val := by simpa only [i,if_pos hp] using hs
          let t := (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse
          let low := prefixInput (SuffixData S n)
            (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b (by omega) t a hal
          have hlow : 2^rxCount a.val b * HammingWeight low.val ≤ HammingWeight t.val := hr
          change (2^rxCount a.val b * 2) * HammingWeight low.val ≤ HammingWeight s.val
          calc
            _ = 2 * (2^rxCount a.val b * HammingWeight low.val) := by ring
            _ ≤ 2 * HammingWeight t.val := Nat.mul_le_mul_left 2 hlow
            _ ≤ HammingWeight s.val := hs'
        · rw [if_neg hp,Nat.add_zero]
          exact hr.trans (by simpa only [i,if_neg hp,one_mul] using hs)

theorem actual_interval_contraction (s : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    2 ^ rxCount a.val b.val * HammingWeight (actualInputs S n s a).val ≤
      HammingWeight (actualInputs S n s b).val := by
  rw [actualInputs_interval S n s b a ha]
  exact prefix_contraction S n b.val (Nat.le_of_lt_succ b.isLt) _ a ha

/-- Determinism of the unchanged lower suffix after actual input coalescence. -/
theorem inputs_eq_below (s t : TopInput S n) (a b : LevelIndex n)
    (ha : b.val ≤ a.val) (hs : actualInputs S n s a = actualInputs S n t a) :
    actualInputs S n s b = actualInputs S n t b := by
  rw [actualInputs_interval S n s a b ha,actualInputs_interval S n t a b ha,hs]

theorem output_eq_below (s t : TopInput S n) (a : LevelIndex n)
    (hs : actualInputs S n s a = actualInputs S n t a)
    (i : StepIndex n) (hi : i.succ.val ≤ a.val) :
    actualOutput S n s i = actualOutput S n t i := by
  unfold actualOutput
  rw [inputs_eq_below S n s t a i.succ hi hs]

/-- Linear lifting of the actual step-pair equality through every retained
history position, including zero and repeated component words. -/
theorem interval_pair_replay (s t s' t' : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val)
    (hs : ∀ i : StepIndex n, a.val ≤ i.val → i.succ.val ≤ b.val →
      (actualOutput S n s i).correction + (actualOutput S n t i).correction =
        (actualOutput S n s' i).correction + (actualOutput S n t' i).correction) :
    correctionIntervalSum S n s a b + correctionIntervalSum S n t a b =
      correctionIntervalSum S n s' a b + correctionIntervalSum S n t' a b := by
  have aux : ∀ b (hb : b ≤ n) (hab : a.val ≤ b),
      (∀ i : StepIndex n, a.val ≤ i.val → i.succ.val ≤ b →
        (actualOutput S n s i).correction + (actualOutput S n t i).correction =
          (actualOutput S n s' i).correction + (actualOutput S n t' i).correction) →
      correctionIntervalSum S n s a ⟨b,Nat.lt_succ_of_le hb⟩ +
          correctionIntervalSum S n t a ⟨b,Nat.lt_succ_of_le hb⟩ =
        correctionIntervalSum S n s' a ⟨b,Nat.lt_succ_of_le hb⟩ +
          correctionIntervalSum S n t' a ⟨b,Nat.lt_succ_of_le hb⟩ := by
    intro b
    induction b with
    | zero =>
        intro hb hab hs
        have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
        subst a
        simp only [correctionIntervalSum_self]
    | succ b ih =>
        intro hb hab hs
        by_cases he : a.val = b+1
        · have hea : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
          subst a
          simp only [correctionIntervalSum_self]
        · have hal : a.val ≤ b := by omega
          let i : StepIndex n := ⟨b,by omega⟩
          have hlo := ih (by omega) hal (fun j hj hupper => hs j hj (by omega))
          have hstep := hs i hal (by simp [i])
          change correctionIntervalSum S n s a i.castSucc + correctionIntervalSum S n t a i.castSucc =
            correctionIntervalSum S n s' a i.castSucc + correctionIntervalSum S n t' a i.castSucc at hlo
          change correctionIntervalSum S n s a i.succ + correctionIntervalSum S n t a i.succ =
            correctionIntervalSum S n s' a i.succ + correctionIntervalSum S n t' a i.succ
          rw [correctionIntervalSum_succ S n s a i hal,correctionIntervalSum_succ S n t a i hal,
            correctionIntervalSum_succ S n s' a i hal,correctionIntervalSum_succ S n t' a i hal]
          calc
            _ = ((SuffixData S n).selectedMap i).map1
                (correctionIntervalSum S n s a i.castSucc + correctionIntervalSum S n t a i.castSucc) +
              ((actualOutput S n s i).correction + (actualOutput S n t i).correction) := by
                rw [map_add]; abel
            _ = ((SuffixData S n).selectedMap i).map1
                (correctionIntervalSum S n s' a i.castSucc + correctionIntervalSum S n t' a i.castSucc) +
              ((actualOutput S n s' i).correction + (actualOutput S n t' i).correction) := by
                rw [hlo,hstep]
            _ = _ := by rw [map_add]; abel
  exact aux b.val (Nat.le_of_lt_succ b.isLt) hab hs

theorem coalesced_output_pair_zero (s : TopInput S n) (e : TopWord S n)
    (a : LevelIndex n)
    (hs : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (i : StepIndex n) (hi : i.val < a.val) :
    (actualOutput S n s i).correction +
      (actualOutput S n (perturbTop S n s e) i).correction = 0 := by
  rw [output_eq_below S n s (perturbTop S n s e) a hs i (by simp only [Fin.val_succ]; omega)]
  exact binary_word_add_self _

end QEC.Coding.BDL26PairedHistoryQueryCone
