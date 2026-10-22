import QEC.Coding.FiniteAlternatingConstruction.NativePresentationGenerator
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PaidRowsComposition
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.VariableRelabeling

/-!
# Paid native-order caches for the unchanged event-labelled experiment

Project-derived internal refinement of BDL26 paper.tex2120-2198,2221-2258.
The constructor takes only scale/depth, a continuous table and explicitly
external materialized event supports. It constructs its own rows and native
address enumeration. Original event/rank preprocessing and event selection are
external to the bounded cache interpreter. They are neither implemented nor
charged as free cache operations. Native row order is never identified with
the original equivFin order. Costs count finite-record/cursor unit operations,
table reads and allocations, not integer bit complexity or hardware execution.
-/
namespace QEC.Coding.BDL26NativeStateRows

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Operations and allocations instrument the same value-producing branches. -/
structure Run (A : Type*) where
  value : A
  operations : ℕ
  allocations : ℕ

def mapQ {A B : Type*} (f : A → Run B) : List A → Run (List B)
  | [] => ⟨[],0,0⟩
  | a::as =>
      let x := f a
      let xs := mapQ f as
      ⟨x.value::xs.value,x.operations+xs.operations+3,
        x.allocations+xs.allocations+1⟩

theorem map_value {A B : Type*} (f : A → Run B) (L : List A) :
    (mapQ f L).value=L.map (fun a => (f a).value) := by
  induction L <;> simp_all [mapQ]

theorem map_operations {A B : Type*} (f : A → Run B) (L : List A) (c : ℕ)
    (hc : ∀ a∈L,(f a).operations≤c) :
    (mapQ f L).operations≤L.length*(c+3) := by
  induction L with
  | nil => simp [mapQ]
  | cons a L ih =>
      have ha := hc a (by simp)
      have ht := ih (fun b hb => hc b (by simp [hb]))
      simp only [mapQ,List.length_cons]
      nlinarith

theorem map_allocations {A B : Type*} (f : A → Run B) (L : List A) (c : ℕ)
    (hc : ∀ a∈L,(f a).allocations≤c) :
    (mapQ f L).allocations≤L.length*(c+1) := by
  induction L with
  | nil => simp [mapQ]
  | cons a L ih =>
      have ha := hc a (by simp)
      have ht := ih (fun b hb => hc b (by simp [hb]))
      simp only [mapQ,List.length_cons]
      nlinarith

private theorem map_operations_const {A B : Type*} (f : A → Run B) (L : List A)
    (c : ℕ) (hc : ∀ a,(f a).operations=c) :
    (mapQ f L).operations=L.length*(c+3) := by
  induction L with
  | nil => simp [mapQ]
  | cons a L ih =>
      change (f a).operations+(mapQ f L).operations+3=(L.length+1)*(c+3)
      rw [hc,ih]
      ring

private theorem map_allocations_const {A B : Type*} (f : A → Run B) (L : List A)
    (c : ℕ) (hc : ∀ a,(f a).allocations=c) :
    (mapQ f L).allocations=L.length*(c+1) := by
  induction L with
  | nil => simp [mapQ]
  | cons a L ih =>
      change (f a).allocations+(mapQ f L).allocations+1=(L.length+1)*(c+1)
      rw [hc,ih]
      ring

/-- Structural bounded addresses. Each successor pays the old-list traversal. -/
def indices : (N : ℕ) → List (Fin N)
  | 0 => []
  | N+1 => 0::(indices N).map Fin.succ

def indicesQ : (N : ℕ) → Run (List (Fin N))
  | 0 => ⟨[],1,0⟩
  | N+1 =>
      let previous := indicesQ N
      let raised := mapQ (fun i : Fin N => ⟨i.succ,1,0⟩) previous.value
      ⟨0::raised.value,previous.operations+raised.operations+2,
        previous.allocations+raised.allocations+1⟩

theorem indices_value (N : ℕ) : (indicesQ N).value=indices N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [indicesQ,indices,map_value,ih]

theorem indices_length (N : ℕ) : (indices N).length=N := by
  induction N <;> simp_all [indices]

theorem indices_complete (N : ℕ) (i : Fin N) : i∈indices N := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [indices]
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,ih j,rfl⟩)

theorem indices_nodup (N : ℕ) : (indices N).Nodup := by
  induction N with
  | zero => simp [indices]
  | succ N ih =>
      rw [indices,List.nodup_cons]
      constructor
      · intro h
        obtain ⟨i,_,hi⟩ := List.mem_map.mp h
        have hv := congrArg Fin.val hi
        simp at hv
      · exact ih.map (by
          intro i j h
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa using hv)

theorem indices_operations (N : ℕ) : (indicesQ N).operations=2*N^2+1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hm := map_operations_const
        (fun i : Fin N => (⟨i.succ,1,0⟩ : Run (Fin (N+1))))
        (indicesQ N).value 1 (fun _ => rfl)
      rw [indices_value,indices_length] at hm
      simp only [indicesQ]
      rw [indices_value,hm,ih]
      ring

theorem indices_allocations (N : ℕ) : (indicesQ N).allocations≤N^2 := by
  induction N with
  | zero => simp [indicesQ]
  | succ N ih =>
      have hm := map_allocations_const
        (fun i : Fin N => (⟨i.succ,1,0⟩ : Run (Fin (N+1))))
        (indicesQ N).value 0 (fun _ => rfl)
      rw [indices_value,indices_length] at hm
      simp only [indicesQ]
      rw [indices_value,hm]
      nlinarith

/-- Reading addresses in generated order recovers the exact native code list. -/
theorem indices_get {A : Type*} (L : List A) :
    (indices L.length).map L.get=L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      have hget : (fun i : Fin L.length => L[i.val])=L.get := by
        funext i
        simp only [List.get_eq_getElem]
      have htail : (indices L.length).map (fun i => L[i.val])=L :=
        (congrArg (fun f => (indices L.length).map f) hget).trans ih
      simpa [indices,List.map_map,Function.comp_def] using
        congrArg (List.cons a) htail

/-- This is the actual list-length scan used by initialization. Its scalar is
computed by recursion, not read from an uncharged cached-count oracle. -/
def lengthQ {A : Type*} : List A → Run ℕ
  | [] => ⟨0,1,0⟩
  | _::L =>
      let rest := lengthQ L
      ⟨rest.value+1,rest.operations+3,rest.allocations⟩

theorem length_value {A : Type*} (L : List A) : (lengthQ L).value=L.length := by
  induction L <;> simp_all [lengthQ]

theorem length_cost {A : Type*} (L : List A) :
    (lengthQ L).operations=3*L.length+1 ∧ (lengthQ L).allocations=0 := by
  induction L with
  | nil => simp [lengthQ]
  | cons a L ih =>
      simp only [lengthQ,List.length_cons]
      exact ⟨by omega,ih.2⟩

private theorem indices_cast {N M : ℕ} (h : N=M) :
    (indices N).map (Fin.cast h)=indices M := by
  subst M
  simp

abbrev Rows (A : Type*) := List (A × ℕ × Space)
abbrev Samples (A : Type*) := A × ℕ → Space

/-- Identity adapter to the original dependent table notation. It retains
every original label, column and value; no table data is supplied or changed. -/
def asTable {A : Type*} (T : Samples A) : Table (X := fun _ : A => Space) :=
  fun p => T p

theorem asTable_read {A : Type*} (T : Samples A) (a : A) (k : ℕ) :
    asTable T (a,k)=T (a,k) := rfl

def rowsFor {A : Type*} (L : List A) (T : Samples A) (c : A → ℕ) : Rows A :=
  L.map (fun a => (a,c a,T (a,c a)))

/-- A genuine draw, zero counter and row payload cost six operations; a row
payload and its list cell are distinct allocations. -/
def initialQ {A : Type*} (T : Samples A) (L : List A) : Run (Rows A) :=
  mapQ (fun a => ⟨(a,0,T (a,0)),6,1⟩) L

theorem initial_value {A : Type*} (T : Samples A) (L : List A) :
    (initialQ T L).value=rowsFor L T (fun _ => 0) := map_value _ _

theorem initial_cost {A : Type*} (T : Samples A) (L : List A) :
    (initialQ T L).operations=9*L.length ∧
      (initialQ T L).allocations=2*L.length := by
  constructor
  · simpa [initialQ,Nat.mul_comm] using map_operations_const
      (fun a => (⟨(a,0,T (a,0)),6,1⟩ : Run (A × ℕ × Space))) L 6 (fun _ => rfl)
  · simpa [initialQ,Nat.mul_comm] using map_allocations_const
      (fun a => (⟨(a,0,T (a,0)),6,1⟩ : Run (A × ℕ × Space))) L 1 (fun _ => rfl)

/-- The equality only transports the dependent Fin type. Its underlying
address is unchanged; row construction and table lookup are paid here. -/
private def sizedInitialQ {N M : ℕ} (h : N=M) (T : Samples (Fin M))
    (L : List (Fin N)) : Run (Rows (Fin M)) :=
  mapQ (fun i => let a := Fin.cast h i; ⟨(a,0,T (a,0)),6,1⟩) L

private theorem sizedInitial_value {N M : ℕ} (h : N=M) (T : Samples (Fin M))
    (L : List (Fin N)) :
    (sizedInitialQ h T L).value=rowsFor (L.map (Fin.cast h)) T (fun _ => 0) := by
  simp [sizedInitialQ,map_value,rowsFor,List.map_map,Function.comp_def]

private theorem sizedInitial_cost {N M : ℕ} (h : N=M) (T : Samples (Fin M))
    (L : List (Fin N)) :
    (sizedInitialQ h T L).operations=9*L.length ∧
      (sizedInitialQ h T L).allocations=2*L.length := by
  constructor
  · simpa [sizedInitialQ,Nat.mul_comm] using map_operations_const
      (fun i : Fin N => (⟨(Fin.cast h i,0,T (Fin.cast h i,0)),6,1⟩ :
        Run (Fin M × ℕ × Space))) L 6 (fun _ => rfl)
  · simpa [sizedInitialQ,Nat.mul_comm] using map_allocations_const
      (fun i : Fin N => (⟨(Fin.cast h i,0,T (Fin.cast h i,0)),6,1⟩ :
        Run (Fin M × ℕ × Space))) L 1 (fun _ => rfl)

def readQ {A : Type*} [DecidableEq A] (a : A) : Rows A → Run (ℕ × Space)
  | [] => ⟨(0,0),1,0⟩
  | row::R => if row.1=a then ⟨row.2,2,0⟩ else
      let rest := readQ a R
      ⟨rest.value,rest.operations+2,rest.allocations⟩

theorem read_first {A : Type*} [DecidableEq A] (a : A) (k : ℕ) (x : Space)
    (R : Rows A) : (readQ a ((a,k,x)::R)).value=(k,x) := by simp [readQ]

theorem read_missing {A : Type*} [DecidableEq A] (a : A) (R : Rows A)
    (ha : a∉R.map Prod.fst) :
    (readQ a R).value=(0,0) ∧ (readQ a R).operations=2*R.length+1 ∧
      (readQ a R).allocations=0 := by
  induction R with
  | nil => simp [readQ]
  | cons row R ih =>
      have hne : row.1≠a := by intro h; exact ha (by simp [h])
      have ht : a∉R.map Prod.fst := fun h => ha (by simp [h])
      have hr := ih ht
      simp only [readQ,if_neg hne,List.length_cons]
      exact ⟨hr.1,by omega,hr.2.2⟩

theorem read_cost {A : Type*} [DecidableEq A] (a : A) (R : Rows A) :
    (readQ a R).operations≤2*R.length+1 ∧ (readQ a R).allocations=0 := by
  induction R with
  | nil => simp [readQ]
  | cons row R ih =>
      by_cases h : row.1=a
      · simp [readQ,h]
        omega
      · simp only [readQ,if_neg h,List.length_cons]
        exact ⟨by omega,ih.2⟩

theorem read_rowsFor {A : Type*} [DecidableEq A] (T : Samples A) (L : List A)
    (c : A → ℕ) (a : A) (ha : a∈L) :
    (readQ a (rowsFor L T c)).value=(c a,T (a,c a)) := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
      by_cases h : b=a
      · subst b; simp [rowsFor,readQ]
      · have ht : a∈L := by simpa only [List.mem_cons,Ne.symm h,false_or] using ha
        simpa only [rowsFor,List.map_cons,readQ,if_neg h] using ih ht

def memberQ {A : Type*} [DecidableEq A] (a : A) : List A → Run Bool
  | [] => ⟨false,1,0⟩
  | b::L => if a=b then ⟨true,2,0⟩ else
      let rest := memberQ a L
      ⟨rest.value,rest.operations+2,rest.allocations⟩

theorem member_value {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (memberQ a L).value=true ↔ a∈L := by
  induction L with
  | nil => simp [memberQ]
  | cons b L ih => by_cases h : a=b <;> simp [memberQ,h,ih]

theorem member_cost {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (memberQ a L).operations≤2*L.length+1 ∧ (memberQ a L).allocations=0 := by
  induction L with
  | nil => simp [memberQ]
  | cons b L ih =>
      by_cases h : a=b
      · simp [memberQ,h]
        omega
      · simp only [memberQ,if_neg h,List.length_cons]
        exact ⟨by omega,ih.2⟩

def advanceList {A : Type*} [DecidableEq A] (U : List A) (c : A → ℕ) : A → ℕ :=
  fun a => c a+if a∈U then 1 else 0

def refreshRowQ {A : Type*} [DecidableEq A] (T : Samples A) (U : List A)
    (row : A × ℕ × Space) : Run (A × ℕ × Space) :=
  let test := memberQ row.1 U
  if test.value then ⟨(row.1,row.2.1+1,T (row.1,row.2.1+1)),test.operations+7,1⟩
  else ⟨row,test.operations+1,0⟩

private theorem refreshRow_label {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (row : A × ℕ × Space) : (refreshRowQ T U row).value.1=row.1 := by
  unfold refreshRowQ
  dsimp only
  split_ifs <;> rfl

private theorem refreshRow_value {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (c : A → ℕ) (a : A) :
    (refreshRowQ T U (a,c a,T (a,c a))).value=
      (a,advanceList U c a,T (a,advanceList U c a)) := by
  by_cases ha : a∈U
  · have ht := (member_value a U).mpr ha
    simp [refreshRowQ,ht,advanceList,ha]
  · have ht : (memberQ a U).value=false := by
      cases h : (memberQ a U).value <;> simp_all [member_value]
    simp [refreshRowQ,ht,advanceList,ha]

private theorem refreshRow_cost {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (row : A × ℕ × Space) :
    (refreshRowQ T U row).operations≤2*U.length+8 ∧
      (refreshRowQ T U row).allocations≤1 := by
  have hm := (member_cost row.1 U).1
  unfold refreshRowQ
  dsimp only
  split_ifs
  · change (memberQ row.1 U).operations+7≤2*U.length+8 ∧ 1≤1
    constructor <;> omega
  · change (memberQ row.1 U).operations+1≤2*U.length+8 ∧ 0≤1
    constructor <;> omega

def refreshQ {A : Type*} [DecidableEq A] (T : Samples A) (U : List A)
    (R : Rows A) : Run (Rows A) := mapQ (refreshRowQ T U) R

theorem refresh_labels {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (R : Rows A) : (refreshQ T U R).value.map Prod.fst=R.map Prod.fst := by
  simp only [refreshQ,map_value,List.map_map]
  apply List.map_congr_left
  intro row _
  exact refreshRow_label T U row

theorem refresh_value {A : Type*} [DecidableEq A] (T : Samples A)
    (U L : List A) (c : A → ℕ) :
    (refreshQ T U (rowsFor L T c)).value=rowsFor L T (advanceList U c) := by
  simp only [refreshQ,map_value,rowsFor,List.map_map]
  apply List.map_congr_left
  intro a _
  exact refreshRow_value T U c a

theorem refresh_cost {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (R : Rows A) :
    (refreshQ T U R).operations≤R.length*(2*U.length+11) ∧
      (refreshQ T U R).allocations≤2*R.length := by
  constructor
  · exact map_operations _ _ _ (fun row _ => (refreshRow_cost T U row).1)
  · simpa [refreshQ,Nat.mul_comm] using
      map_allocations (refreshRowQ T U) R 1 (fun row _ => (refreshRow_cost T U row).2)

/-- The supplied support lists are external event metadata, not an event-order
construction. Repeated labels in a support increment a row only once. -/
def traceCounters {A : Type*} [DecidableEq A] : List (List A) → (A → ℕ) → A → ℕ
  | [],c => c
  | U::trace,c => traceCounters trace (advanceList U c)

def traceWeight {A : Type*} : List (List A) → ℕ
  | [] => 0
  | U::trace => U.length+traceWeight trace

def runFromQ {A : Type*} [DecidableEq A] (T : Samples A)
    (R : Rows A) : List (List A) → Run (Rows A)
  | [] => ⟨R,1,0⟩
  | U::trace =>
      let next := refreshQ T U R
      let rest := runFromQ T next.value trace
      ⟨rest.value,next.operations+rest.operations+2,next.allocations+rest.allocations⟩

theorem trace_value {A : Type*} [DecidableEq A] (T : Samples A)
    (L : List A) (trace : List (List A)) (c : A → ℕ) :
    (runFromQ T (rowsFor L T c) trace).value=rowsFor L T (traceCounters trace c) := by
  induction trace generalizing c with
  | nil => rfl
  | cons U trace ih =>
      change (runFromQ T (refreshQ T U (rowsFor L T c)).value trace).value=_
      rw [refresh_value]
      exact ih _

theorem trace_labels {A : Type*} [DecidableEq A] (T : Samples A)
    (R : Rows A) (trace : List (List A)) :
    (runFromQ T R trace).value.map Prod.fst=R.map Prod.fst := by
  induction trace generalizing R with
  | nil => rfl
  | cons U trace ih => exact (ih _).trans (refresh_labels T U R)

private theorem refresh_length {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (R : Rows A) : (refreshQ T U R).value.length=R.length := by
  have h := congrArg List.length (refresh_labels T U R)
  simpa only [List.length_map] using h

theorem trace_cost {A : Type*} [DecidableEq A] (T : Samples A)
    (R : Rows A) (trace : List (List A)) :
    (runFromQ T R trace).operations≤2*trace.length+1+
      R.length*(2*traceWeight trace+11*trace.length) ∧
    (runFromQ T R trace).allocations≤2*R.length*trace.length := by
  induction trace generalizing R with
  | nil => simp [runFromQ,traceWeight]
  | cons U trace ih =>
      have hr := refresh_cost T U R
      have ht := ih (refreshQ T U R).value
      rw [refresh_length] at ht
      simp only [runFromQ,List.length_cons,traceWeight]
      constructor <;> nlinarith [ht.1,ht.2,hr.1,hr.2]

theorem trace_counters_append {A : Type*} [DecidableEq A]
    (left right : List (List A)) (c : A → ℕ) :
    traceCounters (left++right) c=traceCounters right (traceCounters left c) := by
  induction left generalizing c with
  | nil => rfl
  | cons U left ih => exact ih _

/-- Emission is a real paid traversal; it retains labels even at one image. -/
def emitQ {A : Type*} (R : Rows A) : Run (List (A × Space)) :=
  mapQ (fun row => ⟨(row.1,row.2.2),2,1⟩) R

theorem emit_value {A : Type*} (L : List A) (T : Samples A) (c : A → ℕ) :
    (emitQ (rowsFor L T c)).value=L.map (fun a => (a,T (a,c a))) := by
  simp [emitQ,map_value,rowsFor,List.map_map,Function.comp_def]

theorem emit_cost {A : Type*} (R : Rows A) :
    (emitQ R).operations=5*R.length ∧ (emitQ R).allocations=2*R.length := by
  constructor
  · simpa [emitQ,Nat.mul_comm] using map_operations_const
      (fun row : A × ℕ × Space => (⟨(row.1,row.2.2),2,1⟩ : Run (A × Space))) R 2 (fun _ => rfl)
  · simpa [emitQ,Nat.mul_comm] using map_allocations_const
      (fun row : A × ℕ × Space => (⟨(row.1,row.2.2),2,1⟩ : Run (A × Space))) R 1 (fun _ => rfl)

noncomputable abbrev P (S : OddScale) (n : ℕ) := (state S n).presentation
abbrev count (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.length
abbrev Index (S : OddScale) (n : ℕ) := Fin (count S n)

/-- The same generated output is bound once; no caller supplies addresses/rows. -/
def initializeQ (S : OddScale) (n : ℕ) (T : Samples (Index S n)) : Run (Rows (Index S n)) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let size := lengthQ generated.1.data.vertices
  let addresses := indicesQ size.value
  let rows := sizedInitialQ (length_value generated.1.data.vertices) T addresses.value
  ⟨rows.value,generated.2+size.operations+addresses.operations+rows.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+
      size.allocations+addresses.allocations+rows.allocations+1⟩

theorem initialize_value (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    (initializeQ S n T).value=rowsFor (indices (count S n)) T (fun _ => 0) := by
  unfold initializeQ
  dsimp only
  rw [sizedInitial_value,indices_value,indices_cast]

theorem initialize_order (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    (initializeQ S n T).value.map Prod.fst=indices (count S n) := by
  simp [initialize_value,rowsFor,List.map_map,Function.comp_def]

theorem initialize_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    (initializeQ S n T).operations=
      (BDL26NativePresentationGenerator.setupQ S n).2+2*(count S n)^2+12*count S n+4 ∧
    (initializeQ S n T).allocations≤
      BDL26NativePresentationGenerator.allocatedRecords S n+(count S n)^2+2*count S n+1 := by
  let V := (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices
  have hv := length_value V
  have hl := length_cost V
  have hlen : (indicesQ (lengthQ V).value).value.length=count S n :=
    (congrArg List.length (indices_value _)).trans ((indices_length _).trans hv)
  have hrows := sizedInitial_cost hv T (indicesQ (lengthQ V).value).value
  rw [hlen] at hrows
  have hio : (indicesQ (lengthQ V).value).operations=2*(count S n)^2+1 :=
    (indices_operations _).trans (congrArg (fun N => 2*N^2+1) hv)
  have hia : (indicesQ (lengthQ V).value).allocations≤(count S n)^2 :=
    (indices_allocations _).trans_eq (congrArg (fun N => N^2) hv)
  constructor
  · change (BDL26NativePresentationGenerator.setupQ S n).2+
      (lengthQ V).operations+(indicesQ (lengthQ V).value).operations+
        (sizedInitialQ hv T (indicesQ (lengthQ V).value).value).operations+2=_
    rw [hrows.1,hl.1,hio]
    dsimp only [V,count]
    ring
  · change BDL26NativePresentationGenerator.allocatedRecords S n+
      (lengthQ V).allocations+(indicesQ (lengthQ V).value).allocations+
        (sizedInitialQ hv T (indicesQ (lengthQ V).value).value).allocations+1≤_
    rw [hl.2,hrows.2]
    omega

def executeQ (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (externalSupports : List (List (Index S n))) : Run (Rows (Index S n)) :=
  let initial := initializeQ S n T
  let rest := runFromQ T initial.value externalSupports
  ⟨rest.value,initial.operations+rest.operations+1,initial.allocations+rest.allocations+1⟩

theorem execute_value (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).value=
      rowsFor (indices (count S n)) T (traceCounters trace (fun _ => 0)) := by
  change (runFromQ T (initializeQ S n T).value trace).value=_
  rw [initialize_value]
  exact trace_value T _ _ _

theorem execute_order (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).value.map Prod.fst=indices (count S n) := by
  simp [execute_value,rowsFor,List.map_map,Function.comp_def]

theorem execute_labels_nodup (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    ((executeQ S n T trace).value.map Prod.fst).Nodup := by
  rw [execute_order]
  exact indices_nodup _

theorem execute_read (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) (a : Index S n) :
    (readQ a (executeQ S n T trace).value).value=
      (traceCounters trace (fun _ => 0) a,T (a,traceCounters trace (fun _ => 0) a)) := by
  rw [execute_value]
  exact read_rowsFor T _ _ a (indices_complete _ a)

theorem execute_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).operations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        2*(count S n)^2+12*count S n+6+2*trace.length+
        count S n*(2*traceWeight trace+11*trace.length) ∧
    (executeQ S n T trace).allocations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        (count S n)^2+2*count S n+2+2*count S n*trace.length := by
  have hi := initialize_cost S n T
  have ht := trace_cost T (initializeQ S n T).value trace
  have hlen : (initializeQ S n T).value.length=count S n := by
    have h := congrArg List.length (initialize_order S n T)
    simpa [indices_length] using h
  rw [hlen] at ht
  have hg := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hg
  have ha := BDL26NativePresentationGenerator.allocated_polynomial S n
  change _≤_ ∧ _≤_
  constructor <;> change _+_+1≤_ <;> omega

/-- The retained input record bound ties cache length to the actual accepted
generator polynomial, rather than a supplied list-cardinality budget. -/
theorem native_length_bound (S : OddScale) (n : ℕ) :
    count S n≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 := by
  have h := BDL26NativePresentationGenerator.retained_space S n
  unfold BDL26NativePresentationGenerator.outputRecords at h
  change (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.length≤_
  omega

theorem native_code_order (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    ((initializeQ S n T).value.map Prod.fst).map
        (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.get=
      (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices := by
  rw [initialize_order]
  exact indices_get _

/-- All emitted coordinates, including coincident points, are constructed. -/
def emittedQ (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) : Run (List (Index S n × Space)) :=
  let cache := executeQ S n T trace
  let out := emitQ cache.value
  ⟨out.value,cache.operations+out.operations+1,cache.allocations+out.allocations+1⟩

theorem emitted_value (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (emittedQ S n T trace).value=(indices (count S n)).map
      (fun a => (a,T (a,traceCounters trace (fun _ => 0) a))) := by
  change (emitQ (executeQ S n T trace).value).value=_
  rw [execute_value]
  exact emit_value _ _ _

theorem emitted_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (emittedQ S n T trace).operations=(executeQ S n T trace).operations+5*count S n+1 ∧
    (emittedQ S n T trace).allocations=(executeQ S n T trace).allocations+2*count S n+1 := by
  have hlen : (executeQ S n T trace).value.length=count S n := by
    have h := congrArg List.length (execute_order S n T trace)
    simpa only [List.length_map,indices_length] using h
  have h := emit_cost (executeQ S n T trace).value
  rw [hlen] at h
  exact ⟨congrArg (fun x => (executeQ S n T trace).operations+x+1) h.1,
    congrArg (fun x => (executeQ S n T trace).allocations+x+1) h.2⟩

/-- Seed is a paid nine-row cache even though all points can coincide. -/
theorem seed_rows (S : OddScale) :
    count S 0=9 ∧
    (initializeQ S 0 (fun _ => 0)).value.length=9 ∧
    ∀ row∈(initializeQ S 0 (fun _ => 0)).value,row.2.1=0 ∧ row.2.2=0 := by
  have hc : count S 0=9 := by rfl
  refine ⟨hc,?_,?_⟩
  · simp [initialize_value,rowsFor,indices_length,hc]
  · intro row hr
    rw [initialize_value] at hr
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨rfl,rfl⟩

noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction

/-- Semantic decoding is proof-only and is internally derived from the real
generator's constructed bijection. It is never an interpreter argument. -/
def decode (S : OddScale) (n : ℕ) : Index S n ≃ Vertex (P S n) :=
  (BDL26NativePresentationGenerator.generatedVertexIndex S n).symm

def encodeSamples (S : OddScale) (n : ℕ) (T : Samples (Vertex (P S n))) :
    Samples (Index S n) := fun p => T (decode S n p.1,p.2)

/-- External support data retains each original event label, with its order
unchanged. Its rank/support preprocessing cost is explicitly not included. -/
def supportOf (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    Option (Event (P S n) J r) → List (Index S n)
  | none => []
  | some e => ((eventSupport (P S n) J r e).image (decode S n).symm).toList

theorem supportOf_membership (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r : ℝ) (e : Event (P S n) J r) (a : Index S n) :
    a∈supportOf S n J r (some e) ↔ decode S n a∈eventSupport (P S n) J r e := by
  simp only [supportOf,Finset.mem_toList]
  constructor
  · intro ha
    obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp ha
    simpa only [← hva,Equiv.apply_symm_apply] using hv
  · intro ha
    exact Finset.mem_image.mpr ⟨decode S n a,ha,(decode S n).symm_apply_apply a⟩

theorem supportOf_length (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r : ℝ) (e : Option (Event (P S n) J r)) : (supportOf S n J r e).length≤12 := by
  cases e with
  | none => simp [supportOf]
  | some e =>
      simp only [supportOf,Finset.length_toList]
      exact (Finset.card_image_le).trans (eventSupport_card_le (P S n) J r e)

/-- Replaying the original selected labels supplies metadata, not a second
selection algorithm and not a claimed paid construction of that trace. -/
def originalTrace (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) : ℕ → List (List (Index S n))
  | 0 => []
  | m+1 => originalTrace S n J r lambda K T m++
      [supportOf S n J r (selected (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K) (asTable T) m)]

private theorem traceWeight_append {A : Type*} (left right : List (List A)) :
    traceWeight (left++right)=traceWeight left+traceWeight right := by
  induction left <;> simp_all [traceWeight,Nat.add_assoc]

theorem original_trace_size (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (originalTrace S n J r lambda K T m).length=m ∧
      traceWeight (originalTrace S n J r lambda K T m)≤12*m := by
  induction m with
  | zero => simp [originalTrace,traceWeight]
  | succ m ih =>
      have hs := supportOf_length S n J r
        (selected (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m)
      constructor
      · simp only [originalTrace,List.length_append,List.length_cons,List.length_nil,ih.1]
      · rw [originalTrace,traceWeight_append]
        simp only [traceWeight,Nat.add_zero]
        omega

theorem original_trace_counters (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    traceCounters (originalTrace S n J r lambda K T m) (fun _ => 0)=
      fun a => counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m (decode S n a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [originalTrace,trace_counters_append,ih]
      change advanceList (supportOf S n J r _) _ = _
      cases h : selected (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K) (asTable T) m with
      | none =>
          rw [counters_succ_of_none (X := fun _ : Vertex (P S n) => Space) _ _ (asTable T) m h]
          funext a
          simp [advanceList,supportOf,h]
      | some e =>
          rw [counters_succ_of_some (X := fun _ : Vertex (P S n) => Space) _ _ (asTable T) m e h]
          funext a
          simp only [h,advanceList,advance,supportOf_membership]

/-- Polynomial cache overhead on original finite prefixes. Construction of the
selected event/rank metadata remains external; the full cache work is paid. -/
theorem original_cache_cost (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).operations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        2*(count S n)^2+12*count S n+6+2*m+35*count S n*m ∧
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).allocations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        (count S n)^2+2*count S n+2+2*count S n*m := by
  have h := execute_cost S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)
  have hs := original_trace_size S n J r lambda K T m
  rw [hs.1] at h
  have hw := Nat.mul_le_mul_left (count S n) (Nat.mul_le_mul_left 2 hs.2)
  constructor <;> nlinarith [h.1,h.2]

theorem original_cache_read (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ)
    (v : Vertex (P S n)) :
    (readQ ((decode S n).symm v)
      (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value).value=
      (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m v,
        T (v,counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m v)) := by
  rw [execute_read,original_trace_counters]
  simp only [encodeSamples,Equiv.apply_symm_apply]

def points (S : OddScale) (n : ℕ) (R : Rows (Index S n)) : Index S n → Space :=
  fun a => (readQ a R).value.2

private theorem original_points (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (fun v => points S n
      (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value
        ((decode S n).symm v))=
      assignment (X := fun _ : Vertex (P S n) => Space) (asTable T) (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K) (asTable T) m) := by
  funext v
  exact congrArg Prod.snd (original_cache_read S n J r lambda K T m v)

/-- Two decisions of each same proposition give the same predicate family. -/
private theorem decidableFamily_unique {Ω I : Type*} (B : I → Set Ω)
    (first second : ∀ i, DecidablePred (· ∈ B i)) : first=second := by
  funext i z
  exact Subsingleton.elim _ _

/-- Every supplied original event scan, including empty/repeated labels, is
identified. Native row order cannot change which original event is first. -/
theorem original_event_scan (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ)
    (L : List (Event (P S n) J r)) :
    firstBadFrom (localEvent
      (BDL26RandomPerturbation.VariableRelabeling.pulledSupport (P S n) J r (decode S n))
      (BDL26RandomPerturbation.VariableRelabeling.pulledBad (P S n) J r lambda K (decode S n))) L
      (points S n (executeQ S n (encodeSamples S n T)
        (originalTrace S n J r lambda K T m)).value)=
      firstBadFrom (localEvent (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K)) L
        (assignment (X := fun _ : Vertex (P S n) => Space) (asTable T) (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K) (asTable T) m)) := by
  have hscan := BDL26RandomPerturbation.VariableRelabeling.original_firstBadFrom
    (P S n) J r lambda K (decode S n) L
      (points S n (executeQ S n (encodeSamples S n T)
        (originalTrace S n J r lambda K T m)).value)
  have hd :
      (fun (e : Event (P S n) J r) (z : Vertex (P S n) → Space) =>
        Classical.propDecidable (z ∈ localEvent (X := fun _ : Vertex (P S n) => Space)
          (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) e)) =
        geometricGlobalBadDecidable (P S n) J r lambda K :=
    decidableFamily_unique _ _ _
  rw [hd] at hscan
  exact hscan.trans
      (congrArg (fun z : Vertex (P S n) → Space =>
        firstBadFrom (localEvent (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K)) L z)
        (original_points S n J r lambda K T m))

/-- Full original event-labelled joint law, not only the output marginal.
The equivalence is internally constructed; no new event order or law occurs. -/
theorem original_joint_law (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (radius cutoff : ℝ) (hc : cutoff<1) :
    letI (v : Vertex (P S n)) := vertexLaw_probability (P S n) radius hc v
    letI (a : Index S n) := BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw_probability
      (P S n) radius cutoff hc (decode S n) a
    (tableLaw (BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw
      (P S n) radius cutoff (decode S n))).map
      (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decodedObservation
        (decode S n) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))=
      (tableLaw (vertexLaw (P S n) radius cutoff)).map
        (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation
          (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K)) := by
  exact BDL26RandomPerturbation.VariableRelabeling.original_joint_law
    (P S n) J r lambda K radius cutoff hc (decode S n)

/-- Every emitted native-labelled coordinate is the same original table read
at its actual original execution counter, in the preserved native order. -/
theorem original_emitted_value (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (emittedQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value=
      (indices (count S n)).map (fun a => (a,assignment (X := fun _ : Vertex (P S n) => Space) (asTable T)
        (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m)
        (decode S n a))) := by
  rw [emitted_value,original_trace_counters]
  rfl

end
end QEC.Coding.BDL26NativeStateRows
