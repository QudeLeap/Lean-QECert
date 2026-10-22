import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.JointExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Joint measurability of the original counted geometric queries

The recursive arithmetic lemmas retain the complete `(value, cost)` result.
In particular the zero-denominator branch retains its different operation
count. Finite Boolean folds and first-true scans retain their original list
bookkeeping and short-circuit behavior.
-/

noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

private theorem measurable_decide_set {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → Prop) [DecidablePred p] (hp : MeasurableSet {w | p w}) :
    Measurable (fun w => decide (p w)) := by
  have he : (fun w => decide (p w)) = (fun w => if p w then true else false) := by
    funext w
    by_cases h : p w <;> simp [h]
  rw [he]
  exact Measurable.ite (p := p) hp measurable_const measurable_const

private theorem measurable_query_cost {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] {x : Ω → A × ℕ} {y : Ω → B × ℕ}
    (hx : Measurable x) (hy : Measurable y) (c : ℕ) :
    Measurable (fun w => c + (x w).2 + (y w).2) :=
  (measurable_of_countable (fun t : ℕ × ℕ => c + t.1 + t.2)).comp
    (hx.snd.prodMk hy.snd)

/-- Both executed value and executed arithmetic cost are jointly measurable. -/
theorem measurable_realExpr_run {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) (e : RealExpr) :
    Measurable (fun w => e.run (a w) (z w) (ρ w)) := by
  induction e with
  | constant x => exact measurable_const
  | vertex i j => exact (ha i j).prodMk measurable_const
  | center j => exact (hz j).prodMk measurable_const
  | radius => exact hρ.prodMk measurable_const
  | add x y hx hy =>
      exact (hx.fst.add hy.fst).prodMk (measurable_query_cost hx hy 1)
  | sub x y hx hy =>
      exact (hx.fst.sub hy.fst).prodMk (measurable_query_cost hx hy 1)
  | mul x y hx hy =>
      exact (hx.fst.mul hy.fst).prodMk (measurable_query_cost hx hy 1)
  | div x y hx hy =>
      exact Measurable.ite (measurableSet_eq_fun hy.fst measurable_const)
        (measurable_const.prodMk (measurable_query_cost hx hy 1))
        ((hx.fst.div hy.fst).prodMk (measurable_query_cost hx hy 2))
  | min x y hx hy =>
      exact (hx.fst.min hy.fst).prodMk (measurable_query_cost hx hy 1)
  | max x y hx hy =>
      exact (hx.fst.max hy.fst).prodMk (measurable_query_cost hx hy 1)

/-- The comparison result and its actual cost are proved together. -/
theorem measurable_realTest_run {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) (e : RealTest) :
    Measurable (fun w => e.run (a w) (z w) (ρ w)) := by
  induction e with
  | le x y =>
      have hx := measurable_realExpr_run a z ρ ha hz hρ x
      have hy := measurable_realExpr_run a z ρ ha hz hρ y
      exact (measurable_decide_set _ (measurableSet_le hx.fst hy.fst)).prodMk
        (measurable_query_cost hx hy 1)
  | ne x y =>
      have hx := measurable_realExpr_run a z ρ ha hz hρ x
      have hy := measurable_realExpr_run a z ρ ha hz hρ y
      exact (measurable_decide_set _ (measurableSet_eq_fun hx.fst hy.fst).compl).prodMk
        (measurable_query_cost hx hy 1)
  | both x y hx hy =>
      exact (measurable_of_countable (fun t : (Bool × ℕ) × (Bool × ℕ) =>
        (t.1.1 && t.2.1, 1 + t.1.2 + t.2.2))).comp (hx.prodMk hy)
  | either x y hx hy =>
      exact (measurable_of_countable (fun t : (Bool × ℕ) × (Bool × ℕ) =>
        (t.1.1 || t.2.1, 1 + t.1.2 + t.2.2))).comp (hx.prodMk hy)

theorem measurable_triangleQuery {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) :
    Measurable (fun w => triangleQuery (a w) (z w) (ρ w)) :=
  measurable_realTest_run a z ρ ha hz hρ triangleQueryProgram

theorem measurable_listAllQuery {Ω A : Type*} [MeasurableSpace Ω]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => listAllQuery (fun a => q a w) L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      exact (measurable_of_countable (fun t : (Bool × ℕ) × (Bool × ℕ) =>
        (t.1.1 && t.2.1, t.1.2 + t.2.2 + 1))).comp ((hq a).prodMk ih)

theorem measurable_listAnyQuery {Ω A : Type*} [MeasurableSpace Ω]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => listAnyQuery (fun a => q a w) L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      exact (measurable_of_countable (fun t : (Bool × ℕ) × (Bool × ℕ) =>
        (t.1.1 || t.2.1, t.1.2 + t.2.2 + 1))).comp ((hq a).prodMk ih)

/-- The original first-true scan is measurable with its final clean-scan cost. -/
theorem measurable_scanQuery {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace (Option A)]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (scanQuery q L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      have hc : Measurable (fun w => (q a w).2 + 1) :=
        (measurable_of_countable (fun n : ℕ => n + 1)).comp (hq a).snd
      have ht : Measurable (fun w => (q a w).2 + (scanQuery q L w).2 + 1) :=
        (measurable_of_countable (fun t : ℕ × ℕ => t.1 + t.2 + 1)).comp
          ((hq a).snd.prodMk ih.snd)
      exact Measurable.ite (measurableSet_eq_fun (hq a).fst measurable_const)
        (measurable_const.prodMk hc) (ih.fst.prodMk ht)

/-- Incoming geometry may vary: this includes the arithmetic branch costs. -/
theorem measurable_anchorCloseQuery (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => anchorCloseQuery P J r a b) := by
  apply measurable_realTest_run
  · intro i j
    exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      (measurable_pi_apply (Vertex.x (P.faceX b.1) : Vertex P))
  · intro j
    exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      (measurable_pi_apply (Vertex.x (P.faceX a.1) : Vertex P))
  · exact measurable_const

theorem measurable_eligiblePairQuery (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => eligiblePairQuery P J r a b) := by
  exact (measurable_of_countable (fun t : Bool × ℕ =>
    ((colorMatchQuery P a b).1 && t.1, (colorMatchQuery P a b).2 + t.2 + 1))).comp
    (measurable_anchorCloseQuery P r a b)

/-- Erasing only the fixed finite-set field retains the original eligibility cost. -/
theorem measurable_eligibleListQuery (P : TannerSquarePresentation) (r : ℝ)
    (L : List (Triangle P)) :
    Measurable (fun J : Vertex P → Space =>
      ((eligibleListQuery P J r L).1.2, (eligibleListQuery P J r L).2)) := by
  let unique := dedupQuery (triangleLabelEqQuery P) L
  have hp : Measurable (fun J : Vertex P → Space =>
      listAllQuery (fun a => listAllQuery (eligiblePairQuery P J r a) unique.1) unique.1) :=
    measurable_listAllQuery _ (fun a => measurable_listAllQuery _
      (fun b => measurable_eligiblePairQuery P r a b) unique.1) unique.1
  exact (measurable_of_countable (fun t : Bool × ℕ =>
    (decide (unique.1.length = 4) && t.1, unique.2 + t.2 + unique.1.length + 2))).comp hp

/-- Relabeling keeps the original filtering decisions and every charged operation. -/
theorem filterMapQuery_map_pair {A B C : Type*} (encode : B → C)
    (q : A → Option B × ℕ) (q' : A → Option C × ℕ)
    (hq : ∀ a, q' a = ((q a).1.map encode, (q a).2)) (L : List A) :
    filterMapQuery q' L = ((filterMapQuery q L).1.map encode, (filterMapQuery q L).2) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [filterMapQuery, hq, ih]
      cases h : (q a).1 <;> simp [h]

theorem memberQuery_map_pair {A B : Type*} (encode : A → B)
    (eq : A → A → Bool × ℕ) (eq' : B → B → Bool × ℕ)
    (heq : ∀ a b, eq' (encode a) (encode b) = eq a b) (a : A) (L : List A) :
    memberQuery eq' (encode a) (L.map encode) = memberQuery eq a L := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.map_cons, memberQuery, heq, ih]

theorem dedupQuery_map_pair {A B : Type*} (encode : A → B)
    (eq : A → A → Bool × ℕ) (eq' : B → B → Bool × ℕ)
    (heq : ∀ a b, eq' (encode a) (encode b) = eq a b) (L : List A) :
    dedupQuery eq' (L.map encode) =
      ((dedupQuery eq L).1.map encode, (dedupQuery eq L).2) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.map_cons, dedupQuery, ih, memberQuery_map_pair encode eq eq' heq]
      cases h : (memberQuery eq a (dedupQuery eq L).1).1 <;> simp [h]

theorem orderedInsertQuery_map_pair {A B : Type*} (encode : A → B)
    (cmp : A → A → Bool × ℕ) (cmp' : B → B → Bool × ℕ)
    (hc : ∀ a b, cmp' (encode a) (encode b) = cmp a b) (a : A) (L : List A) :
    orderedInsertQuery cmp' (encode a) (L.map encode) =
      ((orderedInsertQuery cmp a L).1.map encode, (orderedInsertQuery cmp a L).2) := by
  induction L with
  | nil => rfl
  | cons b L ih =>
      simp only [List.map_cons, orderedInsertQuery, hc, ih]
      cases h : (cmp a b).1 <;> simp [h]

theorem sortQuery_map_pair {A B : Type*} (encode : A → B)
    (cmp : A → A → Bool × ℕ) (cmp' : B → B → Bool × ℕ)
    (hc : ∀ a b, cmp' (encode a) (encode b) = cmp a b) (L : List A) :
    sortQuery cmp' (L.map encode) = ((sortQuery cmp L).1.map encode, (sortQuery cmp L).2) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.map_cons, sortQuery, ih, orderedInsertQuery_map_pair encode cmp cmp' hc]

/-- The old input-rank lookup and four-label sort, on the fixed event carrier. -/
def countedMasterKeyQuery (P : TannerSquarePresentation) (e : MasterEvent P) : List ℕ × ℕ :=
  let raw := mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList
  let sorted := sortQuery (fun a b : ℕ => (decide (a ≤ b), 1)) raw.1
  (sorted.1, raw.2 + sorted.2)

def countedMasterCompareQuery (P : TannerSquarePresentation)
    (e f : MasterEvent P) : Bool × ℕ :=
  let E := countedMasterKeyQuery P e
  let F := countedMasterKeyQuery P f
  let q := lexLEQuery E.1 F.1
  (q.1, E.2 + F.2 + q.2)

def countedMasterEqQuery (P : TannerSquarePresentation) (e f : MasterEvent P) : Bool × ℕ :=
  let forward := countedMasterCompareQuery P e f
  let backward := countedMasterCompareQuery P f e
  (forward.1 && backward.1, forward.2 + backward.2 + 1)

theorem countedMasterKeyQuery_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    countedMasterKeyQuery P (eventToMaster P J r e) = eventKeyQuery P J r e := rfl

theorem countedMasterCompareQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r : ℝ) (e f : Event P J r) :
    countedMasterCompareQuery P (eventToMaster P J r e) (eventToMaster P J r f) =
      eventCompareQuery P J r e f := rfl

theorem countedMasterEqQuery_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    countedMasterEqQuery P (eventToMaster P J r e) (eventToMaster P J r f) =
      eventEqQuery P J r e f := rfl

/-- Only countable label lists receive the discrete sigma algebra here. No spatial
state-row list is given a discrete measurable space. -/
local instance countedLabelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance countedLabelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩

theorem measurable_filterMapQuery {Ω A B : Type*} [MeasurableSpace Ω]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (q : A → Ω → Option B × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => filterMapQuery (fun a => q a w) L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      exact (measurable_of_countable
        (fun t : (Option B × ℕ) × (List B × ℕ) =>
          ((match t.1.1 with | none => t.2.1 | some b => b :: t.2.1),
            t.1.2 + t.2.2 + 1))).comp ((hq a).prodMk ih)

/-- Ineligible tuples are removed before scanning, exactly as in the original
counted construction; they are not added as zero-cost disabled scan entries. -/
def countedMasterCandidateQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) : Option (MasterEvent P) × ℕ :=
  let q := eligibleListQuery P J r L
  if hc : L.toFinset.card = 4 then
    (if q.1.2 then some ⟨L.toFinset, hc⟩ else none, q.2 + 1)
  else (none, q.2 + 1)

theorem countedMasterCandidateQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) :
    countedMasterCandidateQuery P J r L =
      ((candidateEventQuery P J hr L).1.map (eventToMaster P J r),
        (candidateEventQuery P J hr L).2) := by
  by_cases hq : (eligibleListQuery P J r L).1.2 = true
  · have hc : L.toFinset.card = 4 := by
      have h := ((eligibleListQuery_correct P J hr L).mp hq).1
      simpa only [eligibleListQuery_set] using h
    simp only [countedMasterCandidateQuery, dif_pos hc, if_pos hq,
      candidateEventQuery, dif_pos hq, Option.map_some]
    apply Prod.ext
    · apply congrArg (fun e : MasterEvent P => some e)
      apply Subtype.ext
      exact (eligibleListQuery_set P J r L).symm
    · rfl
  · simp only [countedMasterCandidateQuery, candidateEventQuery, dif_neg hq,
      if_neg hq, Option.map_none]
    split_ifs <;> rfl

theorem measurable_countedMasterCandidateQuery (P : TannerSquarePresentation)
    (r : ℝ) (L : List (Triangle P)) :
    Measurable (fun J : Vertex P → Space => countedMasterCandidateQuery P J r L) := by
  have hq := measurable_eligibleListQuery P r L
  by_cases hc : L.toFinset.card = 4
  · have hm : Measurable (fun t : Bool × ℕ =>
        (if t.1 then some (⟨L.toFinset, hc⟩ : MasterEvent P) else none, t.2 + 1)) :=
      measurable_of_countable _
    simpa only [countedMasterCandidateQuery, dif_pos hc, Function.comp_def] using hm.comp hq
  · have hm : Measurable (fun n : ℕ => ((none : Option (MasterEvent P)), n + 1)) :=
      measurable_of_countable _
    simpa only [countedMasterCandidateQuery, dif_neg hc, Function.comp_def] using hm.comp hq.snd

def countedMasterRawUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (countedMasterCandidateQuery P J r) tuples.1
  (events.1, tuples.2 + events.2)

def countedMasterUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let raw := countedMasterRawUniverseQuery P J r
  let unique := dedupQuery (countedMasterEqQuery P) raw.1
  let sorted := sortQuery (countedMasterCompareQuery P) unique.1
  (sorted.1, raw.2 + unique.2 + sorted.2)

theorem countedMasterRawUniverseQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) {r : ℝ} (hr : 0 ≤ r) :
    countedMasterRawUniverseQuery P J r =
      ((rawEventUniverseQuery P J hr).1.map (eventToMaster P J r),
        (rawEventUniverseQuery P J hr).2) := by
  simp only [countedMasterRawUniverseQuery, rawEventUniverseQuery,
    filterMapQuery_map_pair (eventToMaster P J r) _ _
      (countedMasterCandidateQuery_original P J hr)]

/-- Full preprocessing conjugacy: original tuples, multiplicities, duplicate
removal, rank comparisons, final list order, and numeric preprocessing cost. -/
theorem countedMasterUniverseQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) {r : ℝ} (hr : 0 ≤ r) :
    countedMasterUniverseQuery P J r =
      ((eventUniverseQuery P J hr).1.map (eventToMaster P J r),
        (eventUniverseQuery P J hr).2) := by
  simp only [countedMasterUniverseQuery, eventUniverseQuery,
    countedMasterRawUniverseQuery_original P J hr,
    dedupQuery_map_pair (eventToMaster P J r) _ _ (countedMasterEqQuery_original P J r),
    sortQuery_map_pair (eventToMaster P J r) _ _ (countedMasterCompareQuery_original P J r)]

theorem measurable_countedMasterUniverseQuery (P : TannerSquarePresentation) (r : ℝ) :
    Measurable (fun J : Vertex P → Space => countedMasterUniverseQuery P J r) := by
  have hraw := measurable_filterMapQuery (fun L J => countedMasterCandidateQuery P J r L)
    (fun L => measurable_countedMasterCandidateQuery P r L)
    (fourTuplesQuery (triangleInputList P)).1
  have hm : Measurable (fun t : List (MasterEvent P) × ℕ =>
      let raw := (t.1, (fourTuplesQuery (triangleInputList P)).2 + t.2)
      let unique := dedupQuery (countedMasterEqQuery P) raw.1
      let sorted := sortQuery (countedMasterCompareQuery P) unique.1
      (sorted.1, raw.2 + unique.2 + sorted.2)) := measurable_of_countable _
  exact hm.comp hraw

/-- A represented row list is exactly the fixed input-label list with its actual
counter and sample addresses. This is stronger than equality of emitted points. -/
theorem StateRowsRep_rows (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (hR : StateRowsRep P T c R) :
    R = (vertexInputList P).map (fun v => (v, c v, T (v, c v))) := by
  have he : R.map id = R.map (fun row => (row.1, c row.1, T (row.1, c row.1))) := by
    apply List.map_congr_left
    intro row hr
    exact Prod.ext rfl (hR.2 row hr)
  rw [List.map_id] at he
  calc
    R = R.map (fun row => (row.1, c row.1, T (row.1, c row.1))) := he
    _ = (R.map Prod.fst).map (fun v => (v, c v, T (v, c v))) := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [hR.1]

theorem measurable_stateRowQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (v : Vertex P) (L : List (Vertex P))
    (f : Vertex P → Ω → ℕ × Space) (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => stateRowQuery v (L.map (fun u => (u, f u w)))) := by
  induction L with
  | nil => exact measurable_const
  | cons u L ih =>
      by_cases hu : u = v
      · simpa only [List.map_cons, stateRowQuery, if_pos hu] using
          (hf u).prodMk (measurable_const : Measurable (fun _ : Ω => (2 : ℕ)))
      · have hc : Measurable (fun w => (stateRowQuery v
            (L.map (fun u => (u, f u w)))).2 + 2) :=
          (measurable_of_countable (fun n : ℕ => n + 2)).comp ih.snd
        simpa only [List.map_cons, stateRowQuery, if_neg hu] using ih.fst.prodMk hc

/-- Snapshot arithmetic has this exact cost on every input, including zeroes. -/
theorem pointSnapshotQuery_cost (lambda : ℝ) (a b : Space) :
    (pointSnapshotQuery lambda a b).2 = 24 := rfl

theorem measurable_pointSnapshotQuery {Ω : Type*} [MeasurableSpace Ω]
    (lambda : ℝ) (a b : Ω → Space) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun w => pointSnapshotQuery lambda (a w) (b w)) := by
  have he : (fun w => pointSnapshotQuery lambda (a w) (b w)) =
      (fun w => (lambda • ((1/2 : ℝ) • a w) + b w, (24 : ℕ))) := by
    funext w
    exact Prod.ext (pointSnapshotQuery_value lambda (a w) (b w))
      (pointSnapshotQuery_cost lambda (a w) (b w))
  rw [he]
  exact (((ha.const_smul (1/2 : ℝ)).const_smul lambda).add hb).prodMk measurable_const

theorem measurable_stateTrianglePointsQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (t : Triangle P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))) := by
  have hr (i : Fin 3) := measurable_stateRowQuery_map P (triangleVertex P t i) L f hf
  have hp : Measurable (fun w => (stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))).1) := by
    apply measurable_pi_lambda
    intro i
    have hj := (measurable_pi_apply (triangleVertex P t i)).comp hJ
    convert (((hj.const_smul (1/2 : ℝ)).const_smul lambda).add (hr i).fst.snd) using 1
    funext w
    simpa only [statePoints, Function.comp_def, Pi.smul_apply, Pi.add_apply] using
      congrFun (stateTrianglePointsQuery_value P (J w) lambda t
        (L.map (fun u => (u, f u w)))) i
  have hc : Measurable (fun w => (stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))).2) := by
    have hm : Measurable (fun z : ℕ × ℕ × ℕ => z.1 + z.2.1 + z.2.2 + 24 + 24 + 24 + 18) :=
      measurable_of_countable _
    simpa only [stateTrianglePointsQuery, pointSnapshotQuery_cost, Function.comp_def] using
      hm.comp ((hr 0).snd.prodMk ((hr 1).snd.prodMk (hr 2).snd))
  exact hp.prodMk hc

theorem measurable_stateTriangleQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (t : Triangle P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) (z : Ω → Space) (hz : Measurable z) :
    Measurable (fun w => stateTriangleQuery P (J w) lambda t
      (L.map (fun u => (u, f u w))) (z w)) := by
  have hp := measurable_stateTrianglePointsQuery_map P lambda t J hJ L f hf
  have hq := measurable_triangleQuery
    (fun w => (stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))).1) z (fun _ => (2 : ℝ))
    (fun i j => (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      ((measurable_pi_apply i).comp hp.fst))
    (fun j => (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hz)
    measurable_const
  have hc := (measurable_of_countable (fun ns : ℕ × ℕ => ns.1 + ns.2)).comp
    (hp.snd.prodMk hq.snd)
  exact hq.fst.prodMk hc

def countedMasterAnchorQuery (P : TannerSquarePresentation)
    (e : MasterEvent P) : Option (Triangle P) × ℕ :=
  match e.val.toList with
  | [] => (none, 1)
  | a :: L => let q := anchorFoldQuery P a L; (some q.1, q.2 + 1)

def countedMasterStateEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := countedMasterAnchorQuery P e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P J lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1, center.2 + triangles.2 + 8)) net.1
  (query.1, net.2 + anchor.2 + query.2 + 1)

theorem countedMasterStateEventQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    countedMasterStateEventQuery P J lambda K (eventToMaster P J r e) R =
      stateEventQuery P J r lambda K e R := rfl

theorem measurable_fullCenterQuery {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ)
    (a : Option (Triangle P)) (g : Grid K) (J : Ω → Vertex P → Space)
    (hJ : Measurable J) :
    Measurable (fun w => fullCenterQuery P (J w) lambda K a g) := by
  cases a with
  | none => exact measurable_const
  | some t =>
      have hp := measurable_pointSnapshotQuery lambda
        (fun w => J w (.x (P.faceX t.1))) (fun _ : Ω => (gridPointQuery K g).1)
        ((measurable_pi_apply (Vertex.x (P.faceX t.1) : Vertex P)).comp hJ) measurable_const
      have hc := (measurable_of_countable
        (fun n : ℕ => (gridPointQuery K g).2 + n + 2)).comp hp.snd
      exact hp.fst.prodMk hc

theorem measurable_countedMasterStateEventQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ) (e : MasterEvent P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => countedMasterStateEventQuery P (J w) lambda K e
      (L.map (fun u => (u, f u w)))) := by
  let anchor := countedMasterAnchorQuery P e
  have hc (g : Grid K) := measurable_fullCenterQuery P lambda K anchor.1 g J hJ
  have ht (g : Grid K) := measurable_listAllQuery
    (fun a : e.val => fun w => stateTriangleQuery P (J w) lambda a.val
      (L.map (fun u => (u, f u w))) (fullCenterQuery P (J w) lambda K anchor.1 g).1)
    (fun a => measurable_stateTriangleQuery_map P lambda a.val J hJ L f hf _ (hc g).fst)
    (Finset.univ.toList : List e.val)
  have hg (g : Grid K) : Measurable (fun w =>
      let center := fullCenterQuery P (J w) lambda K anchor.1 g
      let triangles := listAllQuery (fun a : e.val =>
        stateTriangleQuery P (J w) lambda a.val (L.map (fun u => (u, f u w))) center.1)
        (Finset.univ.toList : List e.val)
      (triangles.1, center.2 + triangles.2 + 8)) :=
    (ht g).fst.prodMk ((measurable_of_countable
      (fun ns : ℕ × ℕ => ns.1 + ns.2 + 8)).comp ((hc g).snd.prodMk (ht g).snd))
  have hq := measurable_listAnyQuery _ hg (gridListQuery K).1
  exact (measurable_of_countable (fun q : Bool × ℕ =>
    (q.1, (gridListQuery K).2 + anchor.2 + q.2 + 1))).comp hq

theorem countedScan_map_pair {A B W : Type*} (encode : A → B)
    (q : A → W → Bool × ℕ) (q' : B → W → Bool × ℕ)
    (hq : ∀ a w, q' (encode a) w = q a w) (L : List A) (w : W) :
    scanQuery q' (L.map encode) w = ((scanQuery q L w).1.map encode, (scanQuery q L w).2) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.map_cons, scanQuery, hq]
      cases h : (q a w).1 <;> simp [h, ih]

/-- Fixed-carrier scan conjugacy includes numeric costs and the original priority. -/
theorem countedMasterScan_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (countedMasterStateEventQuery P J lambda K)
        (countedMasterUniverseQuery P J r).1 R =
      ((actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).1.map
          (eventToMaster P J r),
        (actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).2) := by
  rw [countedMasterUniverseQuery_original P J hr]
  exact countedScan_map_pair (eventToMaster P J r) _ _
    (countedMasterStateEventQuery_original P J r lambda K) _ R

theorem measurable_actualScanQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w =>
      let R := L.map (fun u => (u, f u w))
      let q := actualScanQuery P (J w) r lambda K (eventUniverseQuery P (J w) hr).1 R
      (q.1.map (eventToMaster P (J w) r), q.2)) := by
  have hm : Measurable (fun z : Ω × List (MasterEvent P) =>
      scanQuery (fun e w => countedMasterStateEventQuery P (J w) lambda K e
        (L.map (fun u => (u, f u w)))) z.2 z.1) :=
    measurable_from_prod_countable_left fun events => measurable_scanQuery _
      (fun e => measurable_countedMasterStateEventQuery_map P lambda K e J hJ L f hf) events
  have he := hm.comp (measurable_id.prodMk
    ((measurable_countedMasterUniverseQuery P r).fst.comp hJ))
  convert he using 1
  funext w
  let R := L.map (fun u => (u, f u w))
  have hscan (events : List (MasterEvent P)) :
      scanQuery (fun e w' => countedMasterStateEventQuery P (J w') lambda K e
        (L.map (fun u => (u, f u w')))) events w =
      scanQuery (countedMasterStateEventQuery P (J w) lambda K) events R := by
    induction events with
    | nil => rfl
    | cons e events ih => simp only [scanQuery, ih, R]
  simpa only [Function.comp_def, id_eq] using
    (countedMasterScan_original P (J w) hr lambda K R).symm.trans (hscan _).symm

theorem mapQuery_map {A B C : Type*} (q : B → C × ℕ) (f : A → B) (L : List A) :
    mapQuery q (L.map f) = mapQuery (fun a => q (f a)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, mapQuery, ih]

theorem mapQuery_cost_congr {A B C : Type*} (q : A → B × ℕ) (q' : A → C × ℕ)
    (hq : ∀ a, (q a).2 = (q' a).2) (L : List A) :
    (mapQuery q L).2 = (mapQuery q' L).2 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [mapQuery, hq, ih]

theorem mapQuery_cost_constant {A B : Type*} (q : A → B × ℕ) (c : ℕ)
    (hq : ∀ a, (q a).2 = c) (L : List A) :
    (mapQuery q L).2 = L.length * (c + 1) := by
  induction L with
  | nil => simp only [mapQuery, List.length_nil, Nat.zero_mul]
  | cons a L ih =>
      simp only [mapQuery, hq, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def countedMasterSupportQuery (P : TannerSquarePresentation)
    (e : MasterEvent P) : List (Vertex P) × ℕ := by
  classical
  let raw := flatMapQuery (fun t : Triangle P =>
    ([triangleVertex P t 0, triangleVertex P t 1, triangleVertex P t 2], 6)) e.val.toList
  let unique := dedupQuery (fun v w : Vertex P => (decide (v = w), 1)) raw.1
  exact (unique.1, raw.2 + unique.2)

def countedMasterRefreshCost (P : TannerSquarePresentation) (e : MasterEvent P) : ℕ :=
  let support := countedMasterSupportQuery P e
  support.2 + (mapQuery (fun v : Vertex P =>
    ((), (memberQuery (fun v w : Vertex P => (decide (v = w), 1)) v support.1).2 + 6))
    (vertexInputList P)).2

theorem countedMasterSupportQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r : ℝ) (e : Event P J r) :
    countedMasterSupportQuery P (eventToMaster P J r e) = supportListQuery P J r e := rfl

/-- Refresh cost uses exactly the original support traversal and stored row labels;
the new sample values and counter magnitudes do not change that traversal. -/
theorem refreshStateRowsQuery_cost_labels (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r : ℝ) (e : Event P J r)
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P)
    (hR : R.map Prod.fst = vertexInputList P) :
    (refreshStateRowsQuery P J r e T R).2 =
      countedMasterRefreshCost P (eventToMaster P J r e) := by
  let support := supportListQuery P J r e
  let q := fun v : Vertex P =>
    ((), (memberQuery (fun v w : Vertex P => (decide (v = w), 1)) v support.1).2 + 6)
  have he : (mapQuery (refreshStateRowQuery support.1 T) R).2 =
      (mapQuery (fun row : Vertex P × ℕ × Space => q row.1) R).2 :=
    mapQuery_cost_congr (refreshStateRowQuery support.1 T)
      (fun row : Vertex P × ℕ × Space => q row.1) (fun _ => rfl) R
  rw [← mapQuery_map q Prod.fst R, hR] at he
  simpa only [refreshStateRowsQuery, countedMasterRefreshCost,
    countedMasterSupportQuery_original] using congrArg (fun n => support.2 + n) he

theorem outputStateRowsQuery_cost (P : TannerSquarePresentation)
    (J : Vertex P → Space) (lambda : ℝ) (R : StateRows P) :
    (outputStateRowsQuery P J lambda R).2 = R.length * 28 :=
  mapQuery_cost_constant _ 27 (fun _ => rfl) R

theorem actualStepQuery_cost_labels (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P)
    (hR : R.map Prod.fst = vertexInputList P) :
    (actualStepQuery P J r lambda K events T R).2 =
      (actualScanQuery P J r lambda K events R).2 +
        match (actualScanQuery P J r lambda K events R).1.map (eventToMaster P J r) with
        | none => 0
        | some e => countedMasterRefreshCost P e := by
  cases hs : (actualScanQuery P J r lambda K events R).1 with
  | none => simp only [actualStepQuery, hs, Option.map_none, Nat.add_zero]
  | some e =>
      simp only [actualStepQuery, hs, Option.map_some]
      rw [refreshStateRowsQuery_cost_labels P J r e T R hR]

/-- Joint row data come from the original counters and original table addresses. -/
theorem measurable_actualScanQuery_prefix (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let events := (eventUniverseQuery P w.1 hr).1
      let R := (actualPrefixQuery P w.1 r lambda K events w.2 n).1
      let q := actualScanQuery P w.1 r lambda K events R
      (q.1.map (eventToMaster P w.1 r), q.2)) := by
  let c := fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
    counters (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2 n
  have hc : Measurable c := measurable_joint_counters P r lambda K n
  have hx := measurable_parameterized_assignment hc
  have hd (v : Vertex P) : Measurable (fun w => (c w v, w.2 (v, c w v))) :=
    ((measurable_pi_apply v).comp hc).prodMk ((measurable_pi_apply v).comp hx)
  have hm := measurable_actualScanQuery_map P hr lambda K
    (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) => w.1)
    measurable_fst (vertexInputList P) (fun v w => (c w v, w.2 (v, c w v))) hd
  convert hm using 1
  funext w
  dsimp only
  rw [StateRowsRep_rows P w.2 (c w) _ (actualPrefixQuery_rep P w.1 hr lambda K w.2 n)]

theorem measurable_actualStepQuery_prefix_cost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let events := (eventUniverseQuery P w.1 hr).1
      let R := (actualPrefixQuery P w.1 r lambda K events w.2 n).1
      (actualStepQuery P w.1 r lambda K events w.2 R).2) := by
  have hs := measurable_actualScanQuery_prefix P hr lambda K n
  have hm : Measurable (fun e : Option (MasterEvent P) =>
      match e with | none => 0 | some e => countedMasterRefreshCost P e) :=
    measurable_of_countable _
  convert hs.snd.add (hm.comp hs.fst) using 1
  funext w
  exact actualStepQuery_cost_labels P w.1 r lambda K _ w.2 _
    (actualPrefixQuery_rep P w.1 hr lambda K w.2 n).1

theorem measurable_actualPrefixQuery_cost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      (actualPrefixQuery P w.1 r lambda K (eventUniverseQuery P w.1 hr).1 w.2 n).2) := by
  induction n with
  | zero =>
      have he (w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space)) :
          (initialRowsQuery P w.2).2 = (vertexInputList P).length * 5 :=
        mapQuery_cost_constant _ 4 (fun _ => rfl) _
      simpa only [actualPrefixQuery, he] using
        (measurable_const : Measurable (fun _ : (Vertex P → Space) ×
          Table (X := fun _ : Vertex P => Space) => (vertexInputList P).length * 5))
  | succ n ih => exact ih.add (measurable_actualStepQuery_prefix_cost P hr lambda K n)

/-- The original stopped numeric cost is jointly measurable, with infinity on
nontermination and the original halt-time zero default left unchanged. -/
theorem measurable_joint_actualExecutionCost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      actualExecutionCost P w.1 hr lambda K w.2) := by
  let Ω := (Vertex P → Space) × Table (X := fun _ : Vertex P => Space)
  have ht := measurable_joint_haltTime P r lambda K
  have hp : Measurable (fun z : Ω × ℕ =>
      (actualPrefixQuery P z.1.1 r lambda K
        (eventUniverseQuery P z.1.1 hr).1 z.1.2 z.2).2) :=
    measurable_from_prod_countable_left (fun n => measurable_actualPrefixQuery_cost P hr lambda K n)
  have hs : Measurable (fun z : Ω × ℕ =>
      (actualScanQuery P z.1.1 r lambda K (eventUniverseQuery P z.1.1 hr).1
        (actualPrefixQuery P z.1.1 r lambda K
          (eventUniverseQuery P z.1.1 hr).1 z.1.2 z.2).1).2) :=
    measurable_from_prod_countable_left (fun n => (measurable_actualScanQuery_prefix P hr lambda K n).snd)
  have hu : Measurable (fun w : Ω => (eventUniverseQuery P w.1 hr).2) := by
    convert (measurable_countedMasterUniverseQuery P r).snd.comp measurable_fst using 1
    funext w
    exact (congrArg Prod.snd (countedMasterUniverseQuery_original P w.1 hr)).symm
  have hstopped := measurable_id.prodMk ht
  have hfinite : Measurable (fun w : Ω =>
      (((eventUniverseQuery P w.1 hr).2 +
        (actualPrefixQuery P w.1 r lambda K (eventUniverseQuery P w.1 hr).1 w.2
          (haltTime (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)).2 +
        (actualScanQuery P w.1 r lambda K (eventUniverseQuery P w.1 hr).1
          (actualPrefixQuery P w.1 r lambda K (eventUniverseQuery P w.1 hr).1 w.2
            (haltTime (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)).1).2 +
        Fintype.card (Vertex P) * 28 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (((hu.add (hp.comp hstopped)).add (hs.comp hstopped)).add_const _)
  convert Measurable.ite (measurableSet_joint_halts P r lambda K) hfinite
    (measurable_const : Measurable (fun _ : Ω => (∞ : ℝ≥0∞))) using 1
  funext w
  by_cases h : Halts (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2
  · simp only [actualExecutionCost, if_pos h, outputStateRowsQuery_cost,
      StateRowsRep_length P w.2 _ _ (actualPrefixQuery_rep P w.1 hr lambda K w.2 _)]
  · simp only [actualExecutionCost, if_neg h]
  exact fun w => Classical.propDecidable
    (Halts (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)

end QEC.Coding.BDL26RandomPerturbation
