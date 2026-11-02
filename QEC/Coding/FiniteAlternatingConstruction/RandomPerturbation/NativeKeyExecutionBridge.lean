import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.KeyedGeometricExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeMasterCandidates
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeGeometricAvoidance
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventUniverse

/-!
# Paid native master-row selection and original-key refinement

All runtime candidates come from the actual native master generator.  Colors,
incoming coordinates, four-key sorting and geometric queries are evaluated by
their counted interpreters.  Semantic decoding labels the resulting rows; it
does not provide an interpreter input or a supplied execution trace.
-/
noncomputable section
namespace QEC.Coding.BDL26NativeKeyExecutionBridge
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

namespace SR
export BDL26NativeStateRows (Index Run Rows Samples decode readQ initializeQ indices
  count rowsFor initialize_value read_rowsFor indices_complete refreshQ refresh_value
  executeQ execute_value execute_read traceCounters trace_counters_append advanceList
  encodeSamples asTable points)
end SR
namespace MC
export BDL26NativeMasterCandidates (Rows Rep codeList masterEquiv master_bijection
  master_nodup master_sound_support master_complete_unique masterCandidatesQ master_value)
end MC
namespace NC
export BDL26NativeTriangleColors (nativeKey nativeKey_injective nativeColor nativeRow
  colorOfCodeQ lookup_actual actual_corner_decode tripleAt)
end NC
namespace MD
abbrev Code := BDL26NativePresentationGenerator.Code
export BDL26NativeSupportMetadata (FourCodes corners triangleCode atlasQ atlasReadQ
  atlas_actual queryQ)
end MD

abbrev Presentation (S : OddScale) (n : ℕ) := BDL26NativeStateRows.P S n
abbrev GeneratedRow (S : OddScale) (n : ℕ) := {row // row ∈ MC.Rows S n}
abbrev Event (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  KeyEvent (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r

def master (S : OddScale) (n : ℕ) (row : GeneratedRow S n) := MC.masterEquiv S n row

theorem row_rep (S : OddScale) (n : ℕ) (row : GeneratedRow S n) :
    MC.Rep S n row.val.1 (master S n row) := (MC.master_bijection S n).2.2 row

/-- Incoming native rows are really initialized by the original generator. -/
def incomingQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) :=
  SR.initializeQ S n (fun p => J (SR.decode S n p.1))

theorem incoming_read (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (a : SR.Index S n) :
    (SR.readQ a (incomingQ S n J).value).value.2 = J (SR.decode S n a) := by
  rw [incomingQ, SR.initialize_value, SR.read_rowsFor _ _ _ a (SR.indices_complete _ a)]

/-- Actual endpoint/color lookups retain every rejected full-code comparison. -/
def pairQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (r : ℝ) (a b : MD.Code) : Bool × ℕ :=
  let A := NC.colorOfCodeQ S n a
  let B := NC.colorOfCodeQ S n b
  match A.value, B.value with
  | some (ca, xa), some (cb, xb) =>
      let I := incomingQ S n J
      let x := SR.readQ ca.1 I.value
      let y := SR.readQ cb.1 I.value
      let close := anchorCloseProgram.run (fun _ => y.value.2) x.value.2 r
      (decide (xa = xb) && close.1,
        A.operations+B.operations+I.operations+x.operations+y.operations+close.2+5)
  | _, _ => (false, A.operations+B.operations+2)

private theorem color_triple_iff (S : OddScale) (n : ℕ)
    (a b : Triangle (Presentation S n)) :
    (NC.nativeColor S n a 0, NC.nativeColor S n a 1, NC.nativeColor S n a 2) =
      (NC.nativeColor S n b 0, NC.nativeColor S n b 1, NC.nativeColor S n b 2) ↔
    NC.nativeColor S n a = NC.nativeColor S n b := by
  constructor
  · intro h
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg (fun x => x.2.1) h
    · exact congrArg (fun x => x.2.2) h
  · intro h
    rw [h]

theorem pair_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle (Presentation S n)) :
    (pairQ S n J r (MD.triangleCode S n a) (MD.triangleCode S n b)).1 = true ↔
      NC.nativeColor S n a = NC.nativeColor S n b ∧
      dist (oldAnchor (Presentation S n) J a) (oldAnchor (Presentation S n) J b) ≤ r := by
  change (pairQ S n J r (BDL26NativeTriangleColors.encode S n a)
    (BDL26NativeTriangleColors.encode S n b)).1 = true ↔ _
  rw [pairQ, NC.lookup_actual, NC.lookup_actual]
  simp only [NC.nativeRow, Bool.and_eq_true, decide_eq_true_eq,
    incoming_read, color_triple_iff]
  have ha := NC.actual_corner_decode S n a (0 : Fin 3)
  have hb := NC.actual_corner_decode S n b (0 : Fin 3)
  change SR.decode S n (MD.corners S n a).1 = _ at ha
  change SR.decode S n (MD.corners S n b).1 = _ at hb
  rw [ha, hb]
  exact and_congr_right fun _ => anchorCloseQuery_correct (Presentation S n) J hr a b

def eligibleQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (r : ℝ) (codes : MD.FourCodes) : Bool × ℕ :=
  listAllQuery (fun a => listAllQuery (pairQ S n J r a) (MC.codeList codes))
    (MC.codeList codes)

theorem eligible_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (row : GeneratedRow S n) :
    (eligibleQ S n J r row.val.1).1 = true ↔
      KeyEligible (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (master S n row).val := by
  simp only [eligibleQ, listAllQuery_correct]
  have hrep := row_rep S n row
  constructor
  · intro h
    refine ⟨(master S n row).property, ?_, ?_⟩
    · intro a ha b hb
      exact ((pair_actual S n J hr a b).mp (h _ ((hrep _).mpr ⟨a,ha,rfl⟩)
        _ ((hrep _).mpr ⟨b,hb,rfl⟩))).1
    · intro a ha b hb
      exact ((pair_actual S n J hr a b).mp (h _ ((hrep _).mpr ⟨a,ha,rfl⟩)
        _ ((hrep _).mpr ⟨b,hb,rfl⟩))).2
  · rintro ⟨_, hc, hd⟩ c hcm d hdm
    obtain ⟨a,ha,rfl⟩ := (hrep c).mp hcm
    obtain ⟨b,hb,rfl⟩ := (hrep d).mp hdm
    exact (pair_actual S n J hr a b).mpr ⟨hc a ha b hb, hd a ha b hb⟩

/-- A live row stores only generated data and its eligibility proof. -/
abbrev LiveRow (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  {row : GeneratedRow S n // KeyEligible (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J r (master S n row).val}

def event (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ)
    (row : LiveRow S n J r) : Event S n J r := ⟨(master S n row.val).val, row.property⟩

theorem event_injective (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Function.Injective (event S n J r) := by
  intro a b h
  apply Subtype.ext
  apply (MC.masterEquiv S n).injective
  apply Subtype.ext
  change (event S n J r a).val = (event S n J r b).val
  exact congrArg (fun e : Event S n J r => e.val) h

def candidateQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (row : GeneratedRow S n) : Option (LiveRow S n J r) × ℕ :=
  let q := eligibleQ S n J r row.val.1
  if h : q.1 = true then (some ⟨row, (eligible_actual S n J hr row).mp h⟩, q.2+1)
  else (none, q.2+1)

theorem candidate_some (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (row : GeneratedRow S n) (live : LiveRow S n J r) :
    (candidateQ S n J hr row).1 = some live ↔ row = live.val := by
  constructor
  · intro h
    dsimp only [candidateQ] at h
    split_ifs at h with ht
    exact congrArg Subtype.val (Option.some.inj h)
  · intro h
    subst row
    have ht := (eligible_actual S n J hr live.val).mpr live.property
    simp only [candidateQ, ht, dif_pos]

def rawUniverseQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (LiveRow S n J r) × ℕ :=
  let generated := MC.masterCandidatesQ S n
  let scanned := filterMapQuery (candidateQ S n J hr) generated.value.attach
  (scanned.1, generated.operations+scanned.2+1)

theorem raw_mem (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (row : LiveRow S n J r) : row ∈ (rawUniverseQ S n J hr).1 := by
  simp only [rawUniverseQ, filterMapQuery_value, List.mem_filterMap]
  exact ⟨row.val, List.mem_attach _ _, (candidate_some S n J hr _ _).mpr rfl⟩

private theorem filterMap_nodup {A B : Type*} (f : A → Option B) (L : List A)
    (hn : L.Nodup)
    (hi : ∀ a ∈ L, ∀ b ∈ L, ∀ c, f a = some c → f b = some c → a = b) :
    (L.filterMap f).Nodup := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.nodup_cons.mp hn
    have ht := ih hL (by intro b hb c hc; exact hi b (by simp [hb]) c (by simp [hc]))
    cases hf : f a with
    | none => simpa only [List.filterMap_cons, hf] using ht
    | some c =>
      simp only [List.filterMap_cons, hf, List.nodup_cons]
      refine ⟨?_, ht⟩
      intro hc
      obtain ⟨b,hb,hbc⟩ := List.mem_filterMap.mp hc
      have he := hi a (by simp) b (by simp [hb]) c hf hbc
      exact ha (he.symm ▸ hb)

theorem raw_nodup (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) : (rawUniverseQ S n J hr).1.Nodup := by
  simp only [rawUniverseQ,filterMapQuery_value]
  change ((MC.Rows S n).attach.filterMap (fun row => (candidateQ S n J hr row).1)).Nodup
  apply filterMap_nodup _ _ (MC.master_nodup S n).1.attach
  intro a ha b hb c hac hbc
  exact ((candidate_some S n J hr a c).mp hac).trans
    ((candidate_some S n J hr b c).mp hbc).symm

theorem event_surjective (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Function.Surjective (event S n J r) := by
  intro e
  let m : MasterEvent (Presentation S n) := ⟨e.val,e.property.1⟩
  let row := (MC.masterEquiv S n).symm m
  have he : master S n row = m := (MC.masterEquiv S n).apply_symm_apply m
  refine ⟨⟨row, ?_⟩, ?_⟩
  · rw [he]
    exact e.property
  · apply Subtype.ext
    change (master S n row).val = e.val
    exact congrArg (fun m : MasterEvent (Presentation S n) => m.val) he

theorem raw_events (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    ((rawUniverseQ S n J hr).1.map (event S n J r)).Nodup ∧
      ((rawUniverseQ S n J hr).1.map (event S n J r)).toFinset = Finset.univ := by
  refine ⟨(raw_nodup S n J hr).map (event_injective S n J r), ?_⟩
  apply Finset.eq_univ_of_forall
  intro e
  obtain ⟨row,rfl⟩ := event_surjective S n J r e
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row,raw_mem S n J hr row,rfl⟩)

/-- Map native raw-key arithmetic, then pay the four-element insertion sort. -/
def fourKeyQ (codes : MD.FourCodes) : List ℕ × ℕ :=
  let raw := mapQuery (fun c =>
    let q := BDL26NativeTriangleKeys.rawKeyQ c
    (q.1,q.2.1)) (MC.codeList codes)
  let sorted := sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1
  (sorted.1,raw.2+sorted.2)

private theorem nat_compare_correct (a b : ℕ) :
    ((decide (a ≤ b),1) : Bool × ℕ).1 = true ↔ a ≤ b := by
  simp

theorem fourKey_length (codes : MD.FourCodes) : (fourKeyQ codes).1.length = 4 := by
  change (sortQuery (fun a b : ℕ => (decide (a ≤ b),1))
    (mapQuery (fun c : MD.Code => (2*c.owner+c.copy,5)) (MC.codeList codes)).1).1.length = 4
  rw [mapQuery_value,sortQuery_value (fun a b : ℕ => (decide (a ≤ b),1))
    (fun a b : ℕ => a ≤ b) nat_compare_correct,List.length_insertionSort,List.length_map]
  rfl

theorem fourKey_cost (codes : MD.FourCodes) : (fourKeyQ codes).2 ≤ 74 := by
  let raw := mapQuery (fun c : MD.Code =>
    let q := BDL26NativeTriangleKeys.rawKeyQ c
    (q.1,q.2.1)) (MC.codeList codes)
  have hr : raw.2 = 24 := rfl
  have hl : raw.1.length = 4 := by
    simp [raw,mapQuery_value,MC.codeList]
  have hs := sortQuery_cost_le (fun a b : ℕ => (decide (a ≤ b),1)) (· ≤ ·)
    (by intro a b; simp) 1 (by intro a b; exact le_rfl) raw.1
  rw [hl] at hs
  change raw.2 + (sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1).2 ≤ 74
  omega

private theorem map_nodup_on {A B : Type*} (f : A → B) (L : List A) (hn : L.Nodup)
    (hi : ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ha,hL⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hL (by intro b hb c hc; exact hi b (by simp [hb]) c (by simp [hc]))⟩
    intro hm
    obtain ⟨b,hb,hba⟩ := List.mem_map.mp hm
    have he := hi b (by simp [hb]) a (by simp) hba
    exact ha (he ▸ hb)

theorem fourKey_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (fourKeyQ row.val.val.1).1 =
      scanKey (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by
  let raw := (MC.codeList row.val.val.1).map (fun c => 2*c.owner+c.copy)
  have hrep := row_rep S n row.val
  have he : raw.toFinset = (event S n J r row).val.image (NC.nativeKey S n) := by
    ext k
    simp only [raw,List.mem_toFinset,List.mem_map,Finset.mem_image]
    constructor
    · rintro ⟨c,hc,rfl⟩
      obtain ⟨a,ha,rfl⟩ := (hrep c).mp hc
      exact ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨MD.triangleCode S n a,(hrep _).mpr ⟨a,ha,rfl⟩,rfl⟩
  have hn : raw.Nodup := by
    obtain ⟨m,U,hU,hm,hcodes,_,_,_⟩ := MC.master_sound_support S n row.val.val row.val.property
    apply map_nodup_on _ _ hcodes
    intro c hc d hd hcd
    obtain ⟨a,ha,rfl⟩ := (hrep c).mp hc
    obtain ⟨b,hb,rfl⟩ := (hrep d).mp hd
    exact congrArg (MD.triangleCode S n) (NC.nativeKey_injective S n hcd)
  have hp : List.Perm (((event S n J r row).val.image (NC.nativeKey S n)).sort (· ≤ ·)) raw := by
    rw [← he]
    exact (Finset.sort_perm_toList _ _).trans (List.toFinset_toList hn)
  have hs := (hp.trans (List.perm_insertionSort (· ≤ ·) raw).symm).eq_of_pairwise'
    (Finset.pairwise_sort _ _) (List.pairwise_insertionSort _ _)
  change (sortQuery (fun a b : ℕ => (decide (a ≤ b),1))
    (mapQuery (fun c : MD.Code => (2*c.owner+c.copy,5))
      (MC.codeList row.val.val.1)).1).1 = _
  rw [mapQuery_value,sortQuery_value (fun a b : ℕ => (decide (a ≤ b),1))
    (fun a b : ℕ => a ≤ b) nat_compare_correct]
  exact hs.symm

def compareQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ)
    (a b : LiveRow S n J r) : Bool × ℕ :=
  let A := fourKeyQ a.val.val.1
  let B := fourKeyQ b.val.val.1
  let compared := lexLEQuery A.1 B.1
  (compared.1,A.2+B.2+compared.2+1)

theorem compare_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (a b : LiveRow S n J r) :
    (compareQ S n J r a b).1 = true ↔
      keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r a) (event S n J r b) := by
  rw [compareQ,lexLEQuery_correct,fourKey_actual,fourKey_actual]
  rfl

theorem compare_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (a b : LiveRow S n J r) :
    (compareQ S n J r a b).2 ≤ 158 := by
  have ha := fourKey_cost a.val.val.1
  have hb := fourKey_cost b.val.val.1
  have hc := lexLEQuery_cost_le (fourKeyQ a.val.val.1).1 (fourKeyQ b.val.val.1).1
  rw [fourKey_length] at hc
  change (fourKeyQ a.val.val.1).2 + (fourKeyQ b.val.val.1).2 +
    (lexLEQuery (fourKeyQ a.val.val.1).1 (fourKeyQ b.val.val.1).1).2 + 1 ≤ 158
  omega

private theorem map_insert {A B : Type*} (f : A → B) (rel : B → B → Prop)
    [DecidableRel rel] (cmp : A → A → Bool × ℕ)
    (hc : ∀ a b, (cmp a b).1 = true ↔ rel (f a) (f b))
    (a : A) (L : List A) :
    ((orderedInsertQuery cmp a L).1.map f) = (L.map f).orderedInsert rel (f a) := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : rel (f a) (f b)
    · have ht := (hc a b).mpr h
      simp [orderedInsertQuery,ht,h]
    · have ht := Bool.eq_false_iff.mpr (fun h' => h ((hc a b).mp h'))
      simp [orderedInsertQuery,ht,h,ih]

private theorem map_sort {A B : Type*} (f : A → B) (rel : B → B → Prop)
    [DecidableRel rel] (cmp : A → A → Bool × ℕ)
    (hc : ∀ a b, (cmp a b).1 = true ↔ rel (f a) (f b))
    (L : List A) : ((sortQuery cmp L).1.map f) = (L.map f).insertionSort rel := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [sortQuery,List.map_cons,List.insertionSort_cons,map_insert f rel cmp hc,ih]

def universeQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (LiveRow S n J r) × ℕ :=
  let raw := rawUniverseQ S n J hr
  let sorted := sortQuery (compareQ S n J r) raw.1
  (sorted.1,raw.2+sorted.2)

/-- The paid native universe supplies exactly the named keyed order. -/
theorem universe_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    ((universeQ S n J hr).1.map (event S n J r)) =
      (Finset.univ : Finset (Event S n J r)).sort
        (keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r) := by
  have hraw := raw_events S n J hr
  let priority := keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r
  have hp : List.Perm ((Finset.univ : Finset (Event S n J r)).sort priority)
      ((rawUniverseQ S n J hr).1.map (event S n J r)) := by
    rw [← hraw.2]
    exact (Finset.sort_perm_toList _ _).trans (List.toFinset_toList hraw.1)
  have hs := (hp.trans (List.perm_insertionSort priority _).symm).eq_of_pairwise'
    (Finset.pairwise_sort _ _) (List.pairwise_insertionSort _ _)
  change ((sortQuery (compareQ S n J r) _).1.map _) = _
  rw [map_sort (event S n J r) priority (compareQ S n J r) (compare_actual S n J r)]
  exact hs.symm

/-- A local finite sort bound, separate from any expectation of total operations. -/
theorem universe_sort_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).2 ≤ (rawUniverseQ S n J hr).2 +
      ((rawUniverseQ S n J hr).1.length+1)^2*159 := by
  have h := sortQuery_cost_le (compareQ S n J r)
    (fun a b => keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
      J r (event S n J r a) (event S n J r b))
    (compare_actual S n J r) 158 (compare_cost S n J r) (rawUniverseQ S n J hr).1
  change (rawUniverseQ S n J hr).2 + (sortQuery (compareQ S n J r) _).2 ≤ _
  exact Nat.add_le_add_left h _

/-- The generated support payload is consumed directly, without a caller atlas. -/
def support (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ)
    (row : LiveRow S n J r) : List (SR.Index S n) := row.val.val.2.getD []

private theorem rep_unique (S : OddScale) (n : ℕ) (codes : MD.FourCodes)
    (m k : MasterEvent (Presentation S n)) (hm : MC.Rep S n codes m)
    (hk : MC.Rep S n codes k) : m = k := by
  apply Subtype.ext
  ext t
  constructor
  · intro ht
    obtain ⟨u,hu,he⟩ := (hk _).mp ((hm _).mpr ⟨t,ht,rfl⟩)
    have he' := BDL26NativeTriangleKeys.encode_injective S n he
    exact he' ▸ hu
  · intro ht
    obtain ⟨u,hu,he⟩ := (hm _).mp ((hk _).mpr ⟨t,ht,rfl⟩)
    have he' := BDL26NativeTriangleKeys.encode_injective S n he
    exact he' ▸ hu

/-- Every original address is present exactly once, including every copy/parity. -/
theorem support_complete (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (support S n J r row).Nodup ∧ (support S n J r row).length = 12 ∧
    ∀ a, a ∈ support S n J r row ↔ SR.decode S n a ∈
      keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by
  obtain ⟨m,U,hU,hm,_,hUn,hUl,hUm⟩ :=
    MC.master_sound_support S n row.val.val row.val.property
  have he := rep_unique S n row.val.val.1 m (master S n row.val) hm (row_rep S n row.val)
  subst m
  have hmem : ∀ a, a ∈ support S n J r row ↔ SR.decode S n a ∈
      keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by
    simpa only [support,hU,Option.getD_some,keySupport,masterSupport,event] using hUm
  have himage : (support S n J r row).toFinset.image (SR.decode S n) =
      keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by
    ext v
    simp only [Finset.mem_image,List.mem_toFinset]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (hmem a).mp ha
    · intro hv
      refine ⟨(SR.decode S n).symm v,?_,(SR.decode S n).apply_symm_apply v⟩
      exact (hmem _).mpr (by simpa using hv)
  have hn : (support S n J r row).Nodup := by simpa [support,hU] using hUn
  refine ⟨hn,?_,hmem⟩
  calc
    (support S n J r row).length = (support S n J r row).toFinset.card :=
      (List.toFinset_card_of_nodup hn).symm
    _ = ((support S n J r row).toFinset.image (SR.decode S n)).card :=
      (Finset.card_image_of_injective _ (SR.decode S n).injective).symm
    _ = 12 := by rw [himage]; exact keySupport_card_eq_twelve _ _ _ _ _ _

/-- The original assignment is recovered only by the proved native equivalence. -/
def originalPoints (S : OddScale) (n : ℕ) (R : SR.Rows (SR.Index S n)) :
    Vertex (Presentation S n) → Space := fun v => SR.points S n R ((SR.decode S n).symm v)

def pointQ (S : OddScale) (n : ℕ) (lambda : ℝ)
    (I R : SR.Rows (SR.Index S n)) (a : SR.Index S n) : Space × ℕ :=
  let j := SR.readQ a I
  let w := SR.readQ a R
  let q := pointSnapshotQuery lambda j.value.2 w.value.2
  (q.1,j.operations+w.operations+q.2+2)

theorem point_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (a : SR.Index S n) :
    (pointQ S n lambda (incomingQ S n J).value R a).1 =
      lambda • ((1/2 : ℝ) • J (SR.decode S n a)) +
        originalPoints S n R (SR.decode S n a) := by
  simp only [pointQ,pointSnapshotQuery_value,incoming_read,originalPoints,
    Equiv.symm_apply_apply,SR.points]

def triangleCodeQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (c : MD.Code) (center : Space) : Bool × ℕ :=
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ c atlas.value
  match found.value with
  | none => (false,atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n J
      let x := pointQ S n lambda I.value R v.1
      let y := pointQ S n lambda I.value R v.2.1
      let z := pointQ S n lambda I.value R v.2.2
      let q := triangleQuery ![x.1,y.1,z.1] center 2
      (q.1,atlas.operations+found.operations+I.operations+x.2+y.2+z.2+q.2+4)

theorem triangle_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (a : Triangle (Presentation S n))
    (center : Space) :
    (triangleCodeQ S n J lambda R (MD.triangleCode S n a) center).1 = true ↔
      (fun i => originalPoints S n R (triangleVertex (Presentation S n) a i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a i)))
        center 2 := by
  rw [triangleCodeQ, MD.atlas_actual]
  have hx := NC.actual_corner_decode S n a (0 : Fin 3)
  have hy := NC.actual_corner_decode S n a (1 : Fin 3)
  have hz := NC.actual_corner_decode S n a (2 : Fin 3)
  change SR.decode S n (MD.corners S n a).1 = _ at hx
  change SR.decode S n (MD.corners S n a).2.1 = _ at hy
  change SR.decode S n (MD.corners S n a).2.2 = _ at hz
  simp only [point_actual,hx,hy,hz]
  have hs : ![
      lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a 0)) +
        originalPoints S n R (triangleVertex (Presentation S n) a 0),
      lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a 1)) +
        originalPoints S n R (triangleVertex (Presentation S n) a 1),
      lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a 2)) +
        originalPoints S n R (triangleVertex (Presentation S n) a 2)] =
      (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a i)) +
        originalPoints S n R (triangleVertex (Presentation S n) a i)) := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  simp only [triangleQuery_correct _ _ (by norm_num : (0 : ℝ) ≤ 2),
    triangleHit,Set.mem_setOf_eq]

def lowerCodeQ (a b : MD.Code) : MD.Code × ℕ :=
  let A := BDL26NativeTriangleKeys.rawKeyQ a
  let B := BDL26NativeTriangleKeys.rawKeyQ b
  (if A.1 ≤ B.1 then a else b,A.2.1+B.2.1+1)

def anchorFoldQ (a : MD.Code) : List MD.Code → MD.Code × ℕ
  | [] => (a,0)
  | b::L => let lower := lowerCodeQ a b
            let rest := anchorFoldQ lower.1 L
            (rest.1,lower.2+rest.2+1)

private theorem lower_key (a b : MD.Code) :
    2*(lowerCodeQ a b).1.owner+(lowerCodeQ a b).1.copy =
      min (2*a.owner+a.copy) (2*b.owner+b.copy) := by
  change 2*(if 2*a.owner+a.copy ≤ 2*b.owner+b.copy then a else b).owner+
    (if 2*a.owner+a.copy ≤ 2*b.owner+b.copy then a else b).copy = _
  by_cases h : 2*a.owner+a.copy ≤ 2*b.owner+b.copy
  · rw [if_pos h]
    exact (min_eq_left h).symm
  · rw [if_neg h]
    exact (min_eq_right (by omega)).symm

private theorem lower_mem (a b : MD.Code) :
    (lowerCodeQ a b).1=a ∨ (lowerCodeQ a b).1=b := by
  change (if 2*a.owner+a.copy ≤ 2*b.owner+b.copy then a else b)=a ∨
    (if 2*a.owner+a.copy ≤ 2*b.owner+b.copy then a else b)=b
  split_ifs <;> simp

theorem anchorFold_mem (a : MD.Code) (L : List MD.Code) : (anchorFoldQ a L).1 ∈ a::L := by
  induction L generalizing a with
  | nil => simp [anchorFoldQ]
  | cons b L ih =>
    have hr := ih (lowerCodeQ a b).1
    simp only [List.mem_cons] at hr
    rcases hr with h | h
    · rcases lower_mem a b with ha | hb
      · exact List.mem_cons.mpr (Or.inl (h.trans ha))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (h.trans hb))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem anchorFold_min (a : MD.Code) (L : List MD.Code) :
    ∀ c ∈ a::L, 2*(anchorFoldQ a L).1.owner+(anchorFoldQ a L).1.copy ≤ 2*c.owner+c.copy := by
  induction L generalizing a with
  | nil =>
    intro c hc
    have he := List.mem_singleton.mp hc
    subst c
    exact le_rfl
  | cons b L ih =>
    have hh := ih (lowerCodeQ a b).1
    have hlow := hh (lowerCodeQ a b).1 (by simp)
    rw [lower_key] at hlow
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · subst c
      exact hlow.trans (min_le_left _ _)
    · rcases List.mem_cons.mp hc with hc | hc
      · subst c
        exact hlow.trans (min_le_right _ _)
      · exact hh c (List.mem_cons_of_mem _ hc)

def anchorCodeQ (codes : MD.FourCodes) : MD.Code × ℕ :=
  anchorFoldQ codes.first [codes.second,codes.third,codes.fourth]

theorem anchor_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (anchorCodeQ row.val.val.1).1 = MD.triangleCode S n
      (keyAnchor (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row)) := by
  have hrep := row_rep S n row.val
  have hm : (anchorCodeQ row.val.val.1).1 ∈ MC.codeList row.val.val.1 :=
    anchorFold_mem _ _
  obtain ⟨a,ha,he⟩ := (hrep _).mp hm
  have hmin : ∀ b ∈ (event S n J r row).val, NC.nativeKey S n a ≤ NC.nativeKey S n b := by
    intro b hb
    have h := anchorFold_min row.val.val.1.first
      [row.val.val.1.second,row.val.val.1.third,row.val.val.1.fourth]
      (MD.triangleCode S n b) ((hrep _).mpr ⟨b,hb,rfl⟩)
    change 2*(anchorCodeQ row.val.val.1).1.owner+(anchorCodeQ row.val.val.1).1.copy ≤ _ at h
    rw [← he] at h
    exact h
  have hanchor := keyAnchor_unique (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J r (event S n J r row) a ha hmin
  exact he.symm.trans (congrArg (MD.triangleCode S n) hanchor.symm)

def centerQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (K : ℕ) (codes : MD.FourCodes) (g : Grid K) : Space × ℕ :=
  let anchor := anchorCodeQ codes
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ anchor.1 atlas.value
  match found.value with
  | none => (0,anchor.2+atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n J
      let j := SR.readQ v.1 I.value
      let grid := gridPointQuery K g
      let point := pointSnapshotQuery lambda j.value.2 grid.1
      (point.1,anchor.2+atlas.operations+found.operations+I.operations+j.operations+grid.2+point.2+3)

theorem center_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (g : Grid K) :
    (centerQ S n J lambda K row.val.val.1 g).1 =
      keyCenter (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r lambda K (event S n J r row) g := by
  dsimp only [centerQ]
  rw [anchor_actual S n J r row,MD.atlas_actual]
  simp only [pointSnapshotQuery_value,incoming_read,gridPointQuery_value]
  have h := NC.actual_corner_decode S n
    (keyAnchor (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
      J r (event S n J r row)) (0 : Fin 3)
  change SR.decode S n (MD.corners S n _).1 = _ at h
  rw [h]
  rfl

def eventQueryQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (r lambda : ℝ) (K : ℕ) (row : LiveRow S n J r)
    (R : SR.Rows (SR.Index S n)) : Bool × ℕ :=
  let net := gridListQuery K
  let query := listAnyQuery (fun g =>
    let center := centerQ S n J lambda K row.val.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n J lambda R c center.1)
      (MC.codeList row.val.val.1)
    (triangles.1,center.2+triangles.2+2)) net.1
  (query.1,net.2+query.2+1)

theorem query_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (R : SR.Rows (SR.Index S n)) :
    (eventQueryQ S n J r lambda K row R).1 = true ↔
      originalPoints S n R ∈ localEvent
        (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
        (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
          J r lambda K) (event S n J r row) := by
  rw [mem_keyEvent]
  simp only [eventQueryQ,listAnyQuery_correct,listAllQuery_correct,center_actual]
  have hrep := row_rep S n row.val
  constructor
  · rintro ⟨g,hg,ht⟩
    refine ⟨g,?_⟩
    intro a
    exact (triangle_actual S n J lambda R a.val _).mp
      (ht (MD.triangleCode S n a.val) ((hrep _).mpr ⟨a.val,a.property,rfl⟩))
  · rintro ⟨g,ht⟩
    refine ⟨g,gridListQuery_complete K g,?_⟩
    intro c hc
    obtain ⟨a,ha,rfl⟩ := (hrep c).mp hc
    exact (triangle_actual S n J lambda R a _).mpr (ht ⟨a,ha⟩)

def scanQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (R : SR.Rows (SR.Index S n)) : Option (LiveRow S n J r) × ℕ :=
  let candidates := universeQ S n J hr
  let scan := scanQuery (eventQueryQ S n J r lambda K) candidates.1 R
  (scan.1,candidates.2+scan.2+1)

private theorem scan_map {A B W V : Type*} (f : A → B) (q : A → W → Bool × ℕ)
    (g : W → V) (bad : B → Set V) [∀ b, DecidablePred (· ∈ bad b)]
    (hq : ∀ a w, (q a w).1 = true ↔ g w ∈ bad (f a)) (L : List A) (w : W) :
    ((scanQuery q L w).1.map f) = firstBadFrom bad (L.map f) (g w) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : g w ∈ bad (f a)
    · have ht := (hq a w).mpr h
      simp [scanQuery,firstBadFrom,ht,h]
    · have ht := Bool.eq_false_iff.mpr (fun ht => h ((hq a w).mp ht))
      simp [scanQuery,firstBadFrom,ht,h,ih]

private theorem sorted_select {I W : Type*} [Fintype I] [o : LinearOrder I]
    (bad : I → Set W) [∀ i, DecidablePred (· ∈ bad i)] (priority : I → I → Prop)
    [DecidableRel priority] [IsTrans I priority] [Std.Antisymm priority] [Std.Total priority]
    (hr : ∀ a b, priority a b ↔ a ≤ b) (w : W) :
    firstBadFrom bad ((Finset.univ : Finset I).sort priority) w = select bad w := by
  have hp : List.Pairwise (fun a b : I => a ≤ b)
      ((Finset.univ : Finset I).sort priority) :=
    (Finset.pairwise_sort _ _).imp (fun {a b} hab => (hr a b).mp hab)
  have hs : (Finset.univ : Finset I).sort priority =
      (Finset.univ : Finset I).sort (· ≤ ·) :=
    ((Finset.sort_perm_toList _ _).trans (Finset.sort_perm_toList _ _).symm).eq_of_pairwise'
      hp (Finset.pairwise_sort _ _)
  rw [hs]
  rfl

/-- Selection follows the paid native order; no equality to legacy order is used. -/
theorem scan_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (scanQ S n J hr lambda K R).1.map (event S n J r) =
      select (localEvent
        (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
        (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
          J r lambda K)) (originalPoints S n R) := by
  have h := scan_map (event S n J r) (eventQueryQ S n J r lambda K)
    (originalPoints S n) (localEvent
      (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
      (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r lambda K))
    (query_actual S n J r lambda K) (universeQ S n J hr).1 R
  rw [universe_actual] at h
  have hselect := sorted_select
    (o := keyExecutionOrder (Presentation S n) (NC.nativeKey S n)
      (NC.nativeKey_injective S n) J r)
    (localEvent
      (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
      (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r lambda K))
    (keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
    (fun a b => (priority_iff (Presentation S n) (NC.nativeKey S n)
      (NC.nativeKey_injective S n) J r a b).symm) (originalPoints S n R)
  simpa only [scanQ] using h.trans hselect


end QEC.Coding.BDL26NativeKeyExecutionBridge
