import QEC.Coding.ProbabilisticConstruction.LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort

/-!
# Ordered product-table resampling execution

The state consists only of the next table column for each variable. A finite
ordered scan selects the first currently true local event; exactly its support
advances. Sampling spaces are arbitrary measurable spaces.
-/

namespace QEC.Coding.ProbabilisticConstruction.Resampling

open MeasureTheory ProbabilityTheory

/-- Finite event-selection outputs carry the discrete measurable structure. -/
instance finiteOptionMeasurableSpace {α : Type*} [Fintype α] : MeasurableSpace (Option α) := ⊤

instance finiteOptionMeasurableSingletonClass {α : Type*} [Fintype α] :
    MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩

section OrderedScan

variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

/-- Scan a fixed list of event labels, stopping at the first true event. -/
def firstBadFrom : List I → Ω → Option I
  | [], _ => none
  | i :: tail, ω => if ω ∈ B i then some i else firstBadFrom tail ω

theorem firstBadFrom_none_iff (L : List I) (ω : Ω) :
    firstBadFrom B L ω = none ↔ ∀ i ∈ L, ω ∉ B i := by
  induction L with
  | nil => simp [firstBadFrom]
  | cons i L ih =>
    by_cases hi : ω ∈ B i <;> simp [firstBadFrom, hi, ih]

theorem firstBadFrom_some {L : List I} {ω : Ω} {i : I}
    (h : firstBadFrom B L ω = some i) : i ∈ L ∧ ω ∈ B i := by
  induction L with
  | nil => simp [firstBadFrom] at h
  | cons j L ih =>
    by_cases hj : ω ∈ B j
    · have he : j = i := by simpa [firstBadFrom, hj] using h
      subst j
      exact ⟨by simp, hj⟩
    · have ht : firstBadFrom B L ω = some i := by simpa [firstBadFrom, hj] using h
      obtain ⟨hiL, hi⟩ := ih ht
      exact ⟨List.mem_cons_of_mem _ hiL, hi⟩

theorem firstBadFrom_le [LinearOrder I] {L : List I} (hL : L.Pairwise (· ≤ ·))
    {ω : Ω} {i : I} (hi : firstBadFrom B L ω = some i)
    {j : I} (hj : j ∈ L) (hbad : ω ∈ B j) : i ≤ j := by
  induction L with
  | nil => simp at hj
  | cons k L ih =>
    obtain ⟨hkL, hLL⟩ := List.pairwise_cons.mp hL
    by_cases hk : ω ∈ B k
    · have he : k = i := by simpa [firstBadFrom, hk] using hi
      subst k
      rcases List.mem_cons.mp hj with he | hj
      · exact le_of_eq he.symm
      · exact hkL j hj
    · have hi' : firstBadFrom B L ω = some i := by simpa [firstBadFrom, hk] using hi
      rcases List.mem_cons.mp hj with he | hj
      · exact False.elim (hk (he ▸ hbad))
      · exact ih hLL hi' hj

variable [Fintype I] [LinearOrder I]

/-- The fixed event priority is the increasing enumeration of the finite index type. -/
def select (ω : Ω) : Option I := firstBadFrom B (Finset.univ.sort (· ≤ ·)) ω

theorem select_none_iff (ω : Ω) : select B ω = none ↔ ∀ i, ω ∉ B i := by
  simp [select, firstBadFrom_none_iff]

theorem select_some_bad {ω : Ω} {i : I} (h : select B ω = some i) : ω ∈ B i :=
  (firstBadFrom_some B h).2

theorem select_le {ω : Ω} {i j : I} (hi : select B ω = some i)
    (hj : ω ∈ B j) : i ≤ j :=
  firstBadFrom_le B (Finset.pairwise_sort _ _) hi (by simp) hj

variable [MeasurableSpace Ω] [MeasurableSpace I]

theorem measurable_firstBadFrom (hB : ∀ i, MeasurableSet (B i)) (L : List I) :
    Measurable (firstBadFrom B L) := by
  induction L with
  | nil => exact measurable_const
  | cons i L ih => exact Measurable.ite (hB i) measurable_const ih

theorem measurable_select (hB : ∀ i, MeasurableSet (B i)) : Measurable (select B) :=
  measurable_firstBadFrom B hB _

end OrderedScan

section Execution

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}

/-- A countably infinite independent random table, with one row per variable. -/
abbrev Table := ∀ p : V × ℕ, X p.1

/-- The current column of each variable in the random table. -/
abbrev Counters (V : Type*) := V → ℕ

/-- Read one row with its fixed coordinate type made explicit. -/
def tableRead (R : Table (X := X)) (v : V) (n : ℕ) : X v := R (v, n)

/-- The assignment represented by the current table counters. -/
def assignment (R : Table (X := X)) (c : Counters V) : ∀ v, X v :=
  fun v => tableRead R v (c v)

/-- Advance exactly the coordinates in the resampled event. -/
def advance (vars : I → Finset V) (i : I) (c : Counters V) : Counters V :=
  fun v => c v + if v ∈ vars i then 1 else 0

@[simp] theorem advance_of_mem (vars : I → Finset V) (i : I) (c : Counters V)
    {v : V} (hv : v ∈ vars i) : advance vars i c v = c v + 1 := by
  simp [advance, hv]

@[simp] theorem advance_of_notMem (vars : I → Finset V) (i : I) (c : Counters V)
    {v : V} (hv : v ∉ vars i) : advance vars i c v = c v := by
  simp [advance, hv]

theorem le_advance (vars : I → Finset V) (i : I) (c : Counters V) (v : V) :
    c v ≤ advance vars i c v := Nat.le_add_right _ _

variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

/-- Pulling a decidable local predicate back along coordinate restriction is decidable. -/
instance decidableLocalEvents : ∀ i, DecidablePred (· ∈ localEvent vars bad i) :=
  fun i ω => inferInstanceAs (Decidable ((vars i).restrict ω ∈ bad i))

/-- One transition, including the absorbing clean state. -/
def step (R : Table (X := X)) (c : Counters V) : Counters V :=
  match select (localEvent vars bad) (assignment R c) with
  | none => c
  | some i => advance vars i c

/-- The actual finite-prefix execution, starting with column zero in every row. -/
def counters (R : Table (X := X)) : ℕ → Counters V
  | 0 => fun _ => 0
  | n + 1 => step vars bad R (counters R n)

/-- The event selected at time n; none means the execution has halted. -/
def selected (R : Table (X := X)) (n : ℕ) : Option I :=
  select (localEvent vars bad) (assignment R (counters vars bad R n))

theorem counters_succ_of_none (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) :
    counters vars bad R (n + 1) = counters vars bad R n := by
  unfold selected at h
  simp only [counters, step, h]

theorem counters_succ_of_some (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) :
    counters vars bad R (n + 1) = advance vars i (counters vars bad R n) := by
  unfold selected at h
  simp only [counters, step, h]

theorem selected_some_bad (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) :
    assignment R (counters vars bad R n) ∈ localEvent vars bad i :=
  select_some_bad _ h

theorem selected_none_good (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) :
    ∀ i, assignment R (counters vars bad R n) ∉ localEvent vars bad i :=
  (select_none_iff _ _).mp h

theorem counters_monotone (R : Table (X := X)) (v : V) :
    Monotone (fun n => counters vars bad R n v) := by
  apply monotone_nat_of_le_succ
  intro n
  cases h : selected vars bad R n with
  | none => rw [counters_succ_of_none vars bad R n h]
  | some i => rw [counters_succ_of_some vars bad R n i h]; exact le_advance _ _ _ _

theorem resampled_read_fresh (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) {v : V} (hv : v ∈ vars i) :
    counters vars bad R n v < counters vars bad R (n + 1) v := by
  rw [counters_succ_of_some vars bad R n i h, advance_of_mem vars i _ hv]
  omega

/-- A refreshed column is newer than every column read after an earlier transition. -/
theorem refreshed_columns_strict (R : Table (X := X)) (n m : ℕ) (hnm : n < m)
    (i : I) (hm : selected vars bad R m = some i) {v : V} (hv : v ∈ vars i) :
    counters vars bad R (n + 1) v < counters vars bad R (m + 1) v :=
  lt_of_le_of_lt (counters_monotone vars bad R v (Nat.succ_le_of_lt hnm))
    (resampled_read_fresh vars bad R m i hm hv)

theorem unselected_assignment_unchanged (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) {v : V} (hv : v ∉ vars i) :
    assignment R (counters vars bad R (n + 1)) v =
      assignment R (counters vars bad R n) v := by
  rw [counters_succ_of_some vars bad R n i h]
  change tableRead R v (advance vars i (counters vars bad R n) v) =
    tableRead R v (counters vars bad R n v)
  rw [advance_of_notMem vars i _ hv]

theorem halt_absorbing (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) (k : ℕ) :
    counters vars bad R (n + k) = counters vars bad R n ∧
      selected vars bad R (n + k) = none := by
  induction k with
  | zero => exact ⟨rfl, h⟩
  | succ k ih =>
    have hc : counters vars bad R (n + (k + 1)) = counters vars bad R n := by
      rw [← Nat.add_assoc, counters_succ_of_none vars bad R (n + k) ih.2, ih.1]
    exact ⟨hc, by simpa [selected, hc] using h⟩

end Execution

section Measurability

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

/-- Randomly indexed table lookup is measurable by a countable partition over columns. -/
theorem measurable_assignment {c : Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun R => assignment R (c R)) := by
  apply measurable_pi_lambda
  intro v
  have heval : Measurable (fun p : Table (X := X) × ℕ => tableRead p.1 v p.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply (v, n)
  exact heval.comp (measurable_id.prodMk ((measurable_pi_apply v).comp hc))

theorem measurable_counters (hbad : ∀ i, MeasurableSet (bad i)) (n : ℕ) :
    Measurable (fun R : Table (X := X) => counters vars bad R n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs : Measurable (fun R : Table (X := X) =>
        select (localEvent vars bad) (assignment R (counters vars bad R n))) :=
      (measurable_select _ (measurableSet_localEvent vars bad hbad)).comp
        (measurable_assignment ih)
    have hu : Measurable (fun p : Counters V × Option I =>
        match p.2 with | none => p.1 | some i => advance vars i p.1) :=
      measurable_of_countable _
    exact hu.comp (ih.prodMk hs)

theorem measurable_selected (hbad : ∀ i, MeasurableSet (bad i)) (n : ℕ) :
    Measurable (fun R : Table (X := X) => selected vars bad R n) :=
  (measurable_select _ (measurableSet_localEvent vars bad hbad)).comp
    (measurable_assignment (measurable_counters vars bad hbad n))

/-- The actual table law, with independent fresh entries at every coordinate and column. -/
noncomputable def tableLaw (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)] :
    Measure (Table (X := X)) := Measure.infinitePi (fun p : V × ℕ => ν p.1)

instance (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)] :
    IsProbabilityMeasure (tableLaw ν) := by unfold tableLaw; infer_instance

end Measurability

end QEC.Coding.ProbabilisticConstruction.Resampling
