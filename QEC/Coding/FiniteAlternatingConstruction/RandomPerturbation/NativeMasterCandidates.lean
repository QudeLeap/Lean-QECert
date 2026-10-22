import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeSupportMetadata
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeTriangleKeys
import Mathlib.Data.List.Sublists

/-!
# Paid native four-triangle master candidates

Project-derived internal API for #1598. Runtime code uses only the actual
generator and complete ten-field records. Every candidate repeats the complete
paid support query; every copied append cell is charged. Native position order
chooses representatives, never resampling priority. Original Eligible/priority
sorting below is proof-only and leaves the old rank/color/selected trace external.
Finite-record/cursor costs are neither integer bit costs nor hardware timing.
-/
namespace QEC.Coding.BDL26NativeMasterCandidates

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

abbrev Code := BDL26NativePresentationGenerator.Code
abbrev Run := BDL26NativeStateRows.Run
abbrev FourCodes := BDL26NativeSupportMetadata.FourCodes
abbrev Index := BDL26NativeStateRows.Index
abbrev Quad (A : Type*) := A × A × A × A
noncomputable abbrev P := BDL26NativeStateRows.P

/-- Ten scalar loads, ten field stores and one constructor. -/
def copyCodeQ (c : Code) : Run Code :=
  ⟨{family:=c.family,owner:=c.owner,copy:=c.copy,part:=c.part,
    p:=c.p,q:=c.q,i:=c.i,j:=c.j,k:=c.k,l:=c.l},21,1⟩

theorem copy_spec (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧
      (copyCodeQ c).allocations=1 := by
  cases c
  exact ⟨rfl,rfl,rfl⟩

/-- Copies only the visited left spine, retaining immutable payloads. -/
def appendQ {A : Type*} : List A → List A → Run (List A)
  | [],right => ⟨right,1,0⟩
  | a::left,right =>
      let rest := appendQ left right
      ⟨a::rest.value,rest.operations+2,rest.allocations+1⟩

theorem append_spec {A : Type*} (left right : List A) :
    (appendQ left right).value=left++right ∧
      (appendQ left right).operations=2*left.length+1 ∧
      (appendQ left right).allocations=left.length := by
  induction left with
  | nil => simp [appendQ]
  | cons a left ih =>
      simp only [appendQ,List.cons_append,List.length_cons]
      exact ⟨congrArg (a::·) ih.1,by omega,by omega⟩

/-- Each cursor owns its selected value and its strict suffix. Three binds
and one administrative frame are counted at every nonempty cursor node. -/
def suffixQ {A B : Type*} (f : A → List A → Run (List B)) : List A → Run (List B)
  | [] => ⟨[],1,0⟩
  | a::tail =>
      let left := f a tail
      let right := suffixQ f tail
      let joined := appendQ left.value right.value
      ⟨joined.value,left.operations+right.operations+joined.operations+3,
        left.allocations+right.allocations+joined.allocations+1⟩

def suffixValues {A B : Type*} (f : A → List A → List B) : List A → List B
  | [] => []
  | a::tail => f a tail++suffixValues f tail

theorem suffix_value {A B : Type*} (f : A → List A → Run (List B)) (L : List A) :
    (suffixQ f L).value=suffixValues (fun a tail => (f a tail).value) L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [suffixQ,suffixValues,(append_spec _ _).1,ih]

private theorem map_suffix {A B C : Type*} (g : B → C)
    (f : A → List A → List B) (L : List A) :
    (suffixValues f L).map g=suffixValues (fun a tail => (f a tail).map g) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [suffixValues,List.map_append,ih]

def levelTwoQ {A B : Type*} (f : A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => BDL26NativeStateRows.mapQ (f a) tail) L

def levelThreeQ {A B : Type*} (f : A → A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => levelTwoQ (f a) tail) L

def quadruplesQ {A B : Type*} (f : A → A → A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => levelThreeQ (f a) tail) L

def quadruples {A : Type*} (L : List A) : List (Quad A) :=
  suffixValues (fun a afterA => suffixValues (fun b afterB =>
    suffixValues (fun c afterC => afterC.map (fun d => (a,b,c,d))) afterB) afterA) L

def quadList {A : Type*} (t : Quad A) : List A := [t.1,t.2.1,t.2.2.1,t.2.2.2]

private theorem quadList_injective {A : Type*} : Function.Injective (@quadList A) := by
  rintro ⟨a,b,c,d⟩ ⟨w,x,y,z⟩ h
  simpa only [quadList,List.cons.injEq,Prod.mk.injEq,and_true] using h

theorem quadruples_value {A B : Type*} (f : A → A → A → A → Run B) (L : List A) :
    (quadruplesQ f L).value=
      (quadruples L).map (fun t => (f t.1 t.2.1 t.2.2.1 t.2.2.2).value) := by
  simp only [quadruplesQ,levelThreeQ,levelTwoQ,suffix_value,
    BDL26NativeStateRows.map_value,quadruples,map_suffix,List.map_map,Function.comp_def]

private def combinations {A : Type*} : ℕ → List A → List (List A)
  | 0,_ => [[]]
  | _+1,[] => []
  | k+1,a::L => (combinations k L).map (a::·)++combinations (k+1) L

private theorem combinations_reverse {A : Type*} (k : ℕ) (L : List A) :
    combinations k L=(List.sublistsLen k L).reverse := by
  induction L generalizing k with
  | nil => cases k <;> simp [combinations]
  | cons a L ih =>
      cases k with
      | zero => simp [combinations]
      | succ k =>
          simp only [combinations,List.sublistsLen_succ_cons,List.reverse_append,
            List.map_reverse,ih]

private theorem combinations_suffix {A : Type*} (k : ℕ) (L : List A) :
    combinations (k+1) L=
      suffixValues (fun a tail => (combinations k tail).map (a::·)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [combinations,suffixValues,ih]

private theorem combinations_one {A : Type*} (L : List A) :
    combinations 1 L=L.map (fun a => [a]) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [combinations,ih]

theorem quadruples_lists {A : Type*} (L : List A) :
    (quadruples L).map quadList=(List.sublistsLen 4 L).reverse := by
  rw [←combinations_reverse]
  rw [combinations_suffix 3 L]
  simp only [combinations_suffix 2,combinations_suffix 1,
    combinations_one,quadruples,map_suffix,List.map_map,Function.comp_def,quadList]

theorem quadruples_count {A : Type*} (L : List A) :
    (quadruples L).length=Nat.choose L.length 4 := by
  have h := congrArg List.length (quadruples_lists L)
  simpa only [List.length_map,List.length_reverse,List.length_sublistsLen] using h

theorem quadruples_nodup {A : Type*} (L : List A) (h : L.Nodup) :
    (quadruples L).Nodup := by
  apply List.Nodup.of_map quadList
  rw [quadruples_lists]
  exact List.nodup_reverse.mpr (List.nodup_sublistsLen 4 h)

private theorem quadruples_mem {A : Type*} (L : List A) (t : Quad A) :
    t∈quadruples L ↔ List.Sublist (quadList t) L := by
  have ht : t∈quadruples L ↔ quadList t∈(quadruples L).map quadList := by
    constructor
    · intro h; exact List.mem_map.mpr ⟨t,h,rfl⟩
    · intro h
      obtain ⟨u,hu,he⟩ := List.mem_map.mp h
      exact (quadList_injective he) ▸ hu
  rw [ht,quadruples_lists,List.mem_reverse,List.mem_sublistsLen]
  simp [quadList]

private theorem map_bound {A B : Type*} (f : A → Run B) (L : List A) (p q : ℕ)
    (h : ∀a,(f a).operations≤p ∧ (f a).allocations≤q) :
    (BDL26NativeStateRows.mapQ f L).value.length=L.length ∧
      (BDL26NativeStateRows.mapQ f L).operations≤L.length*(p+3) ∧
      (BDL26NativeStateRows.mapQ f L).allocations≤L.length*(q+1) := by
  induction L with
  | nil => simp [BDL26NativeStateRows.mapQ]
  | cons a L ih =>
      have ha := h a
      simp only [BDL26NativeStateRows.mapQ,List.length_cons]
      exact ⟨congrArg Nat.succ ih.1,by nlinarith [ih.2.1,ha.1],by nlinarith [ih.2.2,ha.2]⟩

private theorem levelTwo_bound {A B : Type*} (f : A → A → Run B) (L : List A) (p q : ℕ)
    (h : ∀a b,(f a b).operations≤p ∧ (f a b).allocations≤q) :
    (levelTwoQ f L).value.length=Nat.choose L.length 2 ∧
      (levelTwoQ f L).operations≤Nat.choose L.length 2*(p+5)+4*L.length+1 ∧
      (levelTwoQ f L).allocations≤Nat.choose L.length 2*(q+2)+L.length := by
  induction L with
  | nil => simp [levelTwoQ,suffixQ]
  | cons a L ih =>
      have hc := map_bound (f a) L p q (h a)
      have hj := append_spec (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
      · change (BDL26NativeStateRows.mapQ (f a) L).operations+(levelTwoQ f L).operations+
          (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).operations+3≤_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (BDL26NativeStateRows.mapQ (f a) L).allocations+(levelTwoQ f L).allocations+
          (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).allocations+1≤_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]

private theorem levelThree_bound {A B : Type*} (f : A → A → A → Run B)
    (L : List A) (p q : ℕ)
    (h : ∀a b c,(f a b c).operations≤p ∧ (f a b c).allocations≤q) :
    (levelThreeQ f L).value.length=Nat.choose L.length 3 ∧
      (levelThreeQ f L).operations≤Nat.choose L.length 3*(p+7)+
        4*(L.length+Nat.choose L.length 2)+1+L.length ∧
      (levelThreeQ f L).allocations≤Nat.choose L.length 3*(q+3)+L.length+Nat.choose L.length 2 := by
  induction L with
  | nil => simp [levelThreeQ,suffixQ]
  | cons a L ih =>
      have hc := levelTwo_bound (f a) L p q (h a)
      have hj := append_spec (levelTwoQ (f a) L).value (levelThreeQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ]
      · change (levelTwoQ (f a) L).operations+(levelThreeQ f L).operations+
          (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).operations+3≤_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (levelTwoQ (f a) L).allocations+(levelThreeQ f L).allocations+
          (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).allocations+1≤_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]

/-- Three structural append levels and one metered fourth-choice map.
The terms count leaves, cursor nodes and exhausted suffixes separately. -/
theorem quadruples_bound {A B : Type*} (f : A → A → A → A → Run B)
    (L : List A) (p q : ℕ)
    (h : ∀a b c d,(f a b c d).operations≤p ∧ (f a b c d).allocations≤q) :
    (quadruplesQ f L).value.length=Nat.choose L.length 4 ∧
      (quadruplesQ f L).operations≤Nat.choose L.length 4*(p+9)+
        4*(L.length+Nat.choose L.length 2+Nat.choose L.length 3)+
          1+L.length+Nat.choose L.length 2 ∧
      (quadruplesQ f L).allocations≤Nat.choose L.length 4*(q+4)+
        L.length+Nat.choose L.length 2+Nat.choose L.length 3 := by
  induction L with
  | nil => simp [quadruplesQ,suffixQ]
  | cons a L ih =>
      have hc := levelThree_bound (f a) L p q (h a)
      have hj := append_spec (levelThreeQ (f a) L).value (quadruplesQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ]
      · change (levelThreeQ (f a) L).operations+(quadruplesQ f L).operations+
          (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).operations+3≤_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (levelThreeQ (f a) L).allocations+(quadruplesQ f L).allocations+
          (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).allocations+1≤_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]

private theorem map_exact {A B : Type*} (f : A → Run B) (L : List A) (p q : ℕ)
    (h : ∀a,(f a).operations=p ∧ (f a).allocations=q) :
    (BDL26NativeStateRows.mapQ f L).value.length=L.length ∧
      (BDL26NativeStateRows.mapQ f L).operations=L.length*(p+3) ∧
      (BDL26NativeStateRows.mapQ f L).allocations=L.length*(q+1) := by
  induction L with
  | nil => simp [BDL26NativeStateRows.mapQ]
  | cons a L ih =>
      have ha := h a
      simp only [BDL26NativeStateRows.mapQ,List.length_cons]
      exact ⟨congrArg Nat.succ ih.1,by nlinarith [ih.2.1,ha.1],by nlinarith [ih.2.2,ha.2]⟩

private theorem levelTwo_exact {A B : Type*} (f : A → A → Run B) (L : List A) (p q : ℕ)
    (h : ∀a b,(f a b).operations=p ∧ (f a b).allocations=q) :
    (levelTwoQ f L).value.length=Nat.choose L.length 2 ∧
      (levelTwoQ f L).operations=Nat.choose L.length 2*(p+5)+4*L.length+1 ∧
      (levelTwoQ f L).allocations=Nat.choose L.length 2*(q+2)+L.length := by
  induction L with
  | nil => simp [levelTwoQ,suffixQ]
  | cons a L ih =>
      have hc := map_exact (f a) L p q (h a)
      have hj := append_spec (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
      · change (BDL26NativeStateRows.mapQ (f a) L).operations+(levelTwoQ f L).operations+
          (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).operations+3=_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (BDL26NativeStateRows.mapQ (f a) L).allocations+(levelTwoQ f L).allocations+
          (appendQ (BDL26NativeStateRows.mapQ (f a) L).value (levelTwoQ f L).value).allocations+1=_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]

private theorem levelThree_exact {A B : Type*} (f : A → A → A → Run B)
    (L : List A) (p q : ℕ)
    (h : ∀a b c,(f a b c).operations=p ∧ (f a b c).allocations=q) :
    (levelThreeQ f L).value.length=Nat.choose L.length 3 ∧
      (levelThreeQ f L).operations=Nat.choose L.length 3*(p+7)+
        4*(L.length+Nat.choose L.length 2)+1+L.length ∧
      (levelThreeQ f L).allocations=Nat.choose L.length 3*(q+3)+L.length+Nat.choose L.length 2 := by
  induction L with
  | nil => simp [levelThreeQ,suffixQ]
  | cons a L ih =>
      have hc := levelTwo_exact (f a) L p q (h a)
      have hj := append_spec (levelTwoQ (f a) L).value (levelThreeQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ]
      · change (levelTwoQ (f a) L).operations+(levelThreeQ f L).operations+
          (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).operations+3=_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (levelTwoQ (f a) L).allocations+(levelThreeQ f L).allocations+
          (appendQ (levelTwoQ (f a) L).value (levelThreeQ f L).value).allocations+1=_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]

/-- Exact resources when the leaf callback has constant resources. -/
theorem quadruples_exact {A B : Type*} (f : A → A → A → A → Run B)
    (L : List A) (p q : ℕ)
    (h : ∀a b c d,(f a b c d).operations=p ∧ (f a b c d).allocations=q) :
    (quadruplesQ f L).value.length=Nat.choose L.length 4 ∧
      (quadruplesQ f L).operations=Nat.choose L.length 4*(p+9)+
        4*(L.length+Nat.choose L.length 2+Nat.choose L.length 3)+
          1+L.length+Nat.choose L.length 2 ∧
      (quadruplesQ f L).allocations=Nat.choose L.length 4*(q+4)+
        L.length+Nat.choose L.length 2+Nat.choose L.length 3 := by
  induction L with
  | nil => simp [quadruplesQ,suffixQ]
  | cons a L ih =>
      have hc := levelThree_exact (f a) L p q (h a)
      have hj := append_spec (levelThreeQ (f a) L).value (quadruplesQ f L).value
      refine ⟨?_,?_,?_⟩
      · change (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).value.length=_
        rw [hj.1,List.length_append,hc.1,ih.1]
        simp only [List.length_cons,Nat.choose_succ_succ]
      · change (levelThreeQ (f a) L).operations+(quadruplesQ f L).operations+
          (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).operations+3=_
        rw [hj.2.1,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.1,ih.2.1]
      · change (levelThreeQ (f a) L).allocations+(quadruplesQ f L).allocations+
          (appendQ (levelThreeQ (f a) L).value (quadruplesQ f L).value).allocations+1=_
        rw [hj.2.2,hc.1]
        simp only [List.length_cons,Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith [hc.2.2,ih.2.2]


/-- Exact overhead census of the SAME suffix/map/append interpreter: C leaves,
K nonempty cursor nodes and E exhausted suffixes. The 9C/4C terms are map
3C/1C plus all THREE append copies 6C/3C. No length scan computes a counter. -/
theorem quadruples_census {A : Type*} (L : List A) :
    let measured := quadruplesQ
      (fun a b c d => (⟨(a,b,c,d),0,0⟩ : Run (Quad A))) L
    measured.value.length=Nat.choose L.length 4 ∧
      measured.operations=9*Nat.choose L.length 4+
        4*(L.length+Nat.choose L.length 2+Nat.choose L.length 3)+
          1+L.length+Nat.choose L.length 2 ∧
      measured.allocations=4*Nat.choose L.length 4+
        L.length+Nat.choose L.length 2+Nat.choose L.length 3 := by
  have h := quadruples_exact (fun a b c d => (⟨(a,b,c,d),0,0⟩ : Run (Quad A)))
    L 0 0 (fun _ _ _ _ => ⟨rfl,rfl⟩)
  simpa only [Nat.zero_add,Nat.mul_comm] using h

def pack (a b c d : Code) : FourCodes := ⟨a,b,c,d⟩
def codeList (codes : FourCodes) : List Code :=
  [codes.first,codes.second,codes.third,codes.fourth]

def candidateQ (S : OddScale) (n : ℕ) (a b c d : Code) :
    Run (FourCodes × Option (List (Index S n))) :=
  let ca := copyCodeQ a
  let cb := copyCodeQ b
  let cc := copyCodeQ c
  let cd := copyCodeQ d
  let codes := pack ca.value cb.value cc.value cd.value
  let queried := BDL26NativeSupportMetadata.queryQ S n codes
  ⟨(codes,queried.value),ca.operations+cb.operations+cc.operations+cd.operations+
      queried.operations+5+3+8,ca.allocations+cb.allocations+cc.allocations+cd.allocations+
      queried.allocations+1+1⟩

theorem candidate_spec (S : OddScale) (n : ℕ) (a b c d : Code) :
    (candidateQ S n a b c d).value=
      (pack a b c d,(BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).value) ∧
      (candidateQ S n a b c d).operations=
        (BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).operations+100 ∧
      (candidateQ S n a b c d).allocations=
        (BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).allocations+6 := by
  simp only [candidateQ,(copy_spec _).1,(copy_spec _).2.1,(copy_spec _).2.2]
  exact ⟨trivial,by omega,by omega⟩

def masterCandidatesQ (S : OddScale) (n : ℕ) :
    Run (List (FourCodes × Option (List (Index S n)))) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let rows := quadruplesQ (candidateQ S n) generated.1.triangles
  ⟨rows.value,generated.2+rows.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+rows.allocations+1⟩

abbrev actualCodes (S : OddScale) (n : ℕ) :=
  (BDL26NativePresentationGenerator.setupQ S n).1.triangles
abbrev Rows (S : OddScale) (n : ℕ) := (masterCandidatesQ S n).value

theorem master_value (S : OddScale) (n : ℕ) :
    Rows S n=(quadruples (actualCodes S n)).map (fun t =>
      (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
        (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value)) := by
  change (quadruplesQ (candidateQ S n) (actualCodes S n)).value=_
  rw [quadruples_value]
  congr 1

theorem master_count (S : OddScale) (n : ℕ) :
    (Rows S n).length=Nat.choose (actualCodes S n).length 4 := by
  rw [master_value,List.length_map,quadruples_count]

theorem master_count_bound (S : OddScale) (n : ℕ) :
    (Rows S n).length≤(actualCodes S n).length^4 := by
  rw [master_count]
  exact Nat.choose_le_pow _ _

theorem master_accounting (S : OddScale) (n : ℕ) :
    (masterCandidatesQ S n).operations=(BDL26NativePresentationGenerator.setupQ S n).2+
      (quadruplesQ (candidateQ S n) (actualCodes S n)).operations+2 ∧
      (masterCandidatesQ S n).allocations=BDL26NativePresentationGenerator.allocatedRecords S n+
        (quadruplesQ (candidateQ S n) (actualCodes S n)).allocations+1 := ⟨rfl,rfl⟩

theorem seed_count (S : OddScale) : (Rows S 0).length=70 := by
  rw [master_count]
  change Nat.choose (BDL26NativePresentationGenerator.setupQ S 0).1.triangles.length 4=70
  rw [BDL26NativeTriangleKeys.seed_codes] <;> rfl

noncomputable section
open scoped Classical

private theorem actual_nodup (S : OddScale) (n : ℕ) : (actualCodes S n).Nodup :=
  (BDL26NativePresentationGenerator.output_label_nodup S n).2.2

theorem same_encoding (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    BDL26NativeTriangleKeys.encode S n t=BDL26NativeSupportMetadata.triangleCode S n t := rfl

private def rawIndex (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    Fin (BDL26NativeTriangleKeys.triangleCount S n) :=
  ⟨2*c.owner+c.copy,by
    obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
    subst c
    exact (BDL26NativeTriangleKeys.nativeTriangleIndex S n t).isLt⟩

private def decodeCode (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    Triangle (P S n) := (BDL26NativeTriangleKeys.nativeTriangleIndex S n).symm (rawIndex S n c hc)

private theorem decode_encode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    decodeCode S n (BDL26NativeTriangleKeys.encode S n t)
      (BDL26NativeTriangleKeys.encode_member S n t)=t := by
  change (BDL26NativeTriangleKeys.nativeTriangleIndex S n).symm
    (BDL26NativeTriangleKeys.nativeTriangleIndex S n t)=t
  exact (BDL26NativeTriangleKeys.index_inverse S n).1 t

private theorem encode_decode (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    BDL26NativeTriangleKeys.encode S n (decodeCode S n c hc)=c := by
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
  change BDL26NativeTriangleKeys.encode S n t=c at ht
  subst c
  rw [decode_encode]

/-- Complete-record representation of the SAME original four-element set. -/
def Rep (S : OddScale) (n : ℕ) (codes : FourCodes) (m : MasterEvent (P S n)) : Prop :=
  ∀c,c∈codeList codes ↔ ∃t∈m.val,BDL26NativeSupportMetadata.triangleCode S n t=c

private theorem Rep_unique (S : OddScale) (n : ℕ) (codes : FourCodes)
    (m k : MasterEvent (P S n)) (hm : Rep S n codes m) (hk : Rep S n codes k) : m=k := by
  apply Subtype.ext
  apply Finset.ext
  intro t
  constructor
  · intro ht
    obtain ⟨u,hu,he⟩ := (hk _).mp ((hm _).mpr ⟨t,ht,rfl⟩)
    have he' : BDL26NativeTriangleKeys.encode S n u=BDL26NativeTriangleKeys.encode S n t := he
    exact (BDL26NativeTriangleKeys.encode_injective S n he') ▸ hu
  · intro ht
    obtain ⟨u,hu,he⟩ := (hm _).mp ((hk _).mpr ⟨t,ht,rfl⟩)
    have he' : BDL26NativeTriangleKeys.encode S n u=BDL26NativeTriangleKeys.encode S n t := he
    exact (BDL26NativeTriangleKeys.encode_injective S n he') ▸ hu

private theorem sublist_filter_identity {A : Type*} (L xs : List A)
    (hd : L.Nodup) (hs : List.Sublist xs L) :
    L.filter (fun a => decide (a∈xs))=xs := by
  have hx : xs.filter (fun a => decide (a∈xs))=xs :=
    List.filter_eq_self.mpr (by intro a ha; simp [ha])
  have hsub := hs.filter (fun a => decide (a∈xs))
  rw [hx] at hsub
  have he : (L.filter (fun a => decide (a∈xs))).toFinset=xs.toFinset := by
    ext a
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨hs.subset ha,ha⟩⟩
  have hl : (L.filter (fun a => decide (a∈xs))).length=xs.length := by
    rw [←List.toFinset_card_of_nodup (hd.filter _),
      ←List.toFinset_card_of_nodup (hd.sublist hs),he]
  exact (hsub.eq_of_length hl.symm).symm

private theorem sublists_same_set {A : Type*} (L xs ys : List A) (hd : L.Nodup)
    (hx : List.Sublist xs L) (hy : List.Sublist ys L) (he : xs.toFinset=ys.toFinset) : xs=ys := by
  have hp : (fun a => decide (a∈xs))=(fun a => decide (a∈ys)) := by
    funext a
    have hh : a∈xs ↔ a∈ys := by
      simpa only [List.mem_toFinset] using Finset.ext_iff.mp he a
    by_cases hx : a∈xs
    · have hy := hh.mp hx
      simp [hx,hy]
    · have hy : a∉ys := fun hy => hx (hh.mpr hy)
      simp [hx,hy]
  calc
    xs=L.filter (fun a => decide (a∈xs)) := (sublist_filter_identity L xs hd hx).symm
    _=L.filter (fun a => decide (a∈ys)) := congrArg (List.filter · L) hp
    _=ys := sublist_filter_identity L ys hd hy

private theorem rep_codes_set (S : OddScale) (n : ℕ) (codes : FourCodes)
    (m : MasterEvent (P S n)) :
    Rep S n codes m ↔ (codeList codes).toFinset=m.val.image (BDL26NativeTriangleKeys.encode S n) := by
  simp only [Rep,Finset.ext_iff,List.mem_toFinset,Finset.mem_image,same_encoding]

private def originalSet (S : OddScale) (n : ℕ) (codes : FourCodes) : Finset (Triangle (P S n)) :=
  Finset.univ.filter (fun t => BDL26NativeTriangleKeys.encode S n t∈codeList codes)

private theorem originalSet_image (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hc : ∀c∈codeList codes,c∈actualCodes S n) :
    (originalSet S n codes).image (BDL26NativeTriangleKeys.encode S n)=(codeList codes).toFinset := by
  ext c
  simp only [Finset.mem_image,originalSet,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  constructor
  · rintro ⟨t,ht,rfl⟩; exact ht
  · intro h
    refine ⟨decodeCode S n c (hc c h),?_,encode_decode S n c (hc c h)⟩
    rw [encode_decode]; exact h

private theorem tuple_master (S : OddScale) (n : ℕ) (t : Quad Code)
    (ht : t∈quadruples (actualCodes S n)) :
    ∃m : MasterEvent (P S n),Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m := by
  have hs : List.Sublist (quadList t) (actualCodes S n) := (quadruples_mem _ _).mp ht
  have hn : (quadList t).Nodup := (actual_nodup S n).sublist hs
  let codes := pack t.1 t.2.1 t.2.2.1 t.2.2.2
  have hh : ∀c∈codeList codes,c∈actualCodes S n := by
    intro c hc
    exact hs.subset hc
  have him := originalSet_image S n codes hh
  have hcard : (originalSet S n codes).card=4 := by
    calc
      (originalSet S n codes).card=
        ((originalSet S n codes).image (BDL26NativeTriangleKeys.encode S n)).card :=
          (Finset.card_image_of_injective _ (BDL26NativeTriangleKeys.encode_injective S n)).symm
      _=(codeList codes).toFinset.card := congrArg Finset.card him
      _=4 := by
        have hcodes : (codeList codes).Nodup := by
          change (quadList t).Nodup
          exact hn
        exact List.toFinset_card_of_nodup hcodes
  exact ⟨⟨originalSet S n codes,hcard⟩,(rep_codes_set _ _ _ _).mpr him.symm⟩

private theorem tuple_unique_for_master (S : OddScale) (n : ℕ) (t u : Quad Code)
    (ht : t∈quadruples (actualCodes S n)) (hu : u∈quadruples (actualCodes S n))
    (m : MasterEvent (P S n))
    (hr : Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m)
    (hs : Rep S n (pack u.1 u.2.1 u.2.2.1 u.2.2.2) m) : t=u := by
  have he : (quadList t).toFinset=(quadList u).toFinset :=
    ((rep_codes_set _ _ _ _).mp hr).trans ((rep_codes_set _ _ _ _).mp hs).symm
  apply quadList_injective
  apply sublists_same_set (actualCodes S n) _ _ (actual_nodup S n)
    ((quadruples_mem _ _).mp ht) ((quadruples_mem _ _).mp hu)
  ext c
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp he c

private theorem master_tuple (S : OddScale) (n : ℕ) (m : MasterEvent (P S n)) :
    ∃t∈quadruples (actualCodes S n),Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m := by
  let target := m.val.image (BDL26NativeTriangleKeys.encode S n)
  let xs := (actualCodes S n).filter (fun c => decide (c∈target))
  have he : xs.toFinset=target := by
    ext c
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hc
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨BDL26NativeTriangleKeys.encode_member S n t,hc⟩
  have hl : xs.length=4 := by
    rw [←List.toFinset_card_of_nodup ((actual_nodup S n).filter _),he]
    exact (Finset.card_image_of_injective _ (BDL26NativeTriangleKeys.encode_injective S n)).trans m.property
  have hm : xs∈(quadruples (actualCodes S n)).map quadList := by
    rw [quadruples_lists,List.mem_reverse,List.mem_sublistsLen]
    exact ⟨List.filter_sublist,hl⟩
  obtain ⟨t,ht,hx⟩ := List.mem_map.mp hm
  refine ⟨t,ht,(rep_codes_set _ _ _ _).mpr ?_⟩
  exact (congrArg List.toFinset hx).trans he

private theorem row_tuple (S : OddScale) (n : ℕ)
    (row : FourCodes × Option (List (Index S n))) (h : row∈Rows S n) :
    ∃t∈quadruples (actualCodes S n),row=
      (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
        (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value) := by
  rw [master_value] at h
  obtain ⟨t,ht,he⟩ := List.mem_map.mp h
  exact ⟨t,ht,he.symm⟩

theorem master_complete_unique (S : OddScale) (n : ℕ) (m : MasterEvent (P S n)) :
    ∃!row : FourCodes × Option (List (Index S n)),row∈Rows S n ∧ Rep S n row.1 m := by
  obtain ⟨t,ht,hr⟩ := master_tuple S n m
  let row := (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
    (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value)
  refine ⟨row,⟨?_,hr⟩,?_⟩
  · rw [master_value]
    exact List.mem_map.mpr ⟨t,ht,rfl⟩
  · intro other ho
    obtain ⟨u,hu,rfl⟩ := row_tuple S n other ho.1
    have he := tuple_unique_for_master S n u t hu ht m ho.2 hr
    subst u
    rfl

theorem master_nodup (S : OddScale) (n : ℕ) :
    (Rows S n).Nodup ∧ ((Rows S n).map Prod.fst).Nodup := by
  have hf : Function.Injective (fun t : Quad Code => pack t.1 t.2.1 t.2.2.1 t.2.2.2) := by
    intro t u he
    apply quadList_injective
    exact congrArg codeList he
  have hn := (quadruples_nodup (actualCodes S n) (actual_nodup S n)).map hf
  have hk : ((Rows S n).map Prod.fst).Nodup := by
    simpa only [master_value,List.map_map,Function.comp_def] using hn
  exact ⟨List.Nodup.of_map Prod.fst hk,hk⟩

private theorem query_four_actual (S : OddScale) (n : ℕ) (a b c d : Triangle (P S n)) :
    ∃U,(BDL26NativeSupportMetadata.queryQ S n
      (pack (BDL26NativeSupportMetadata.triangleCode S n a)
        (BDL26NativeSupportMetadata.triangleCode S n b)
        (BDL26NativeSupportMetadata.triangleCode S n c)
        (BDL26NativeSupportMetadata.triangleCode S n d))).value=some U ∧
      U.Nodup ∧ U.length≤12 ∧ ∀i,i∈U ↔
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) a ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) b ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) c ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) d := by
  let raw := BDL26NativeSupportMetadata.twelve
    (BDL26NativeSupportMetadata.corners S n a) (BDL26NativeSupportMetadata.corners S n b)
    (BDL26NativeSupportMetadata.corners S n c) (BDL26NativeSupportMetadata.corners S n d)
  refine ⟨(BDL26NativeSupportMetadata.dedupQ raw).value,?_,
    BDL26NativeSupportMetadata.dedup_nodup _,?_,?_⟩
  · simp [BDL26NativeSupportMetadata.queryQ,pack,BDL26NativeSupportMetadata.atlas_actual,raw]
  · simpa [raw,BDL26NativeSupportMetadata.twelve] using BDL26NativeSupportMetadata.dedup_length raw
  · intro i
    rw [BDL26NativeSupportMetadata.dedup_membership]
    have hm (x y z w : BDL26NativeSupportMetadata.Triple (Index S n)) :
        i∈BDL26NativeSupportMetadata.twelve x y z w ↔
        i∈BDL26NativeSupportMetadata.tripleList x ∨ i∈BDL26NativeSupportMetadata.tripleList y ∨
        i∈BDL26NativeSupportMetadata.tripleList z ∨ i∈BDL26NativeSupportMetadata.tripleList w := by
      simp [BDL26NativeSupportMetadata.twelve,BDL26NativeSupportMetadata.tripleList,or_assoc]
    rw [hm]
    simp only [BDL26NativeSupportMetadata.corners_membership]

/-- Every physical row succeeds, with every actual X/Q/Z endpoint retained. -/
theorem master_sound_support (S : OddScale) (n : ℕ)
    (row : FourCodes × Option (List (Index S n))) (hrow : row∈Rows S n) :
    ∃m : MasterEvent (P S n),∃U,row.2=some U ∧ Rep S n row.1 m ∧
      (codeList row.1).Nodup ∧ U.Nodup ∧ U.length≤12 ∧
      ∀i,i∈U ↔ BDL26NativeStateRows.decode S n i∈masterSupport (P S n) m := by
  obtain ⟨t,ht,rfl⟩ := row_tuple S n row hrow
  obtain ⟨m,hm⟩ := tuple_master S n t ht
  have hs : List.Sublist (quadList t) (actualCodes S n) := (quadruples_mem _ _).mp ht
  have hn : (quadList t).Nodup := (actual_nodup S n).sublist hs
  have ha : ∃a∈m.val,BDL26NativeSupportMetadata.triangleCode S n a=t.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hb : ∃b∈m.val,BDL26NativeSupportMetadata.triangleCode S n b=t.2.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hc : ∃c∈m.val,BDL26NativeSupportMetadata.triangleCode S n c=t.2.2.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hd : ∃d∈m.val,BDL26NativeSupportMetadata.triangleCode S n d=t.2.2.2 :=
    (hm _).mp (by simp [codeList,pack])
  obtain ⟨a,ham,ha⟩ := ha
  obtain ⟨b,hbm,hb⟩ := hb
  obtain ⟨c,hcm,hc⟩ := hc
  obtain ⟨d,hdm,hd⟩ := hd
  obtain ⟨U,hU,hUn,hUl,hUm⟩ := query_four_actual S n a b c d
  rw [ha,hb,hc,hd] at hU
  refine ⟨m,U,hU,hm,hn,hUn,hUl,?_⟩
  intro i
  rw [hUm]
  simp only [masterSupport,Finset.mem_biUnion]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨a,ham,h⟩
    · exact ⟨b,hbm,h⟩
    · exact ⟨c,hcm,h⟩
    · exact ⟨d,hdm,h⟩
  · rintro ⟨v,hvm,hv⟩
    have hvcode := (hm _).mpr ⟨v,hvm,rfl⟩
    simp only [codeList,pack,List.mem_cons,List.not_mem_nil,or_false] at hvcode
    rcases hvcode with he|he|he|he
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans ha.symm)
      exact Or.inl (he' ▸ hv)
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hb.symm)
      exact Or.inr (Or.inl (he' ▸ hv))
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hc.symm)
      exact Or.inr (Or.inr (Or.inl (he' ▸ hv)))
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hd.symm)
      exact Or.inr (Or.inr (Or.inr (he' ▸ hv)))

def decodeRow (S : OddScale) (n : ℕ) (row : {row // row∈Rows S n}) : MasterEvent (P S n) :=
  Classical.choose (master_sound_support S n row.val row.property)

private theorem decodeRow_rep (S : OddScale) (n : ℕ) (row : {row // row∈Rows S n}) :
    Rep S n row.val.1 (decodeRow S n row) := by
  have h := Classical.choose_spec (master_sound_support S n row.val row.property)
  exact (Classical.choose_spec h).2.1

/-- The inverse is obtained only after actual existence/physical uniqueness is proved. -/
def masterEquiv (S : OddScale) (n : ℕ) : {row // row∈Rows S n} ≃ MasterEvent (P S n) :=
  Equiv.ofBijective (decodeRow S n) (by
    constructor
    · intro a b he
      apply Subtype.ext
      have ha := decodeRow_rep S n a
      have hb := decodeRow_rep S n b
      rw [←he] at hb
      obtain ⟨row,hr,hu⟩ := master_complete_unique S n (decodeRow S n a)
      exact (hu a.val ⟨a.property,ha⟩).trans (hu b.val ⟨b.property,hb⟩).symm
    · intro m
      obtain ⟨row,hr,_⟩ := master_complete_unique S n m
      refine ⟨⟨row,hr.1⟩,?_⟩
      exact Rep_unique S n row.1 _ _ (decodeRow_rep S n ⟨row,hr.1⟩) hr.2)

theorem master_bijection (S : OddScale) (n : ℕ) :
    (∀row,(masterEquiv S n).symm (masterEquiv S n row)=row) ∧
      (∀m,masterEquiv S n ((masterEquiv S n).symm m)=m) ∧
      ∀row,Rep S n row.val.1 (masterEquiv S n row) :=
  ⟨(masterEquiv S n).symm_apply_apply,(masterEquiv S n).apply_symm_apply,decodeRow_rep S n⟩

theorem eligible_support (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    ∃!row : FourCodes × Option (List (Index S n)),row∈Rows S n ∧
      Rep S n row.1 (eventToMaster (P S n) J r e) ∧
      ∃U,row.2=some U ∧ U.Nodup ∧ U.length≤12 ∧
        ∀i,i∈U ↔ BDL26NativeStateRows.decode S n i∈eventSupport (P S n) J r e := by
  obtain ⟨row,hr,hu⟩ := master_complete_unique S n (eventToMaster (P S n) J r e)
  refine ⟨row,⟨hr.1,hr.2,?_⟩,?_⟩
  · obtain ⟨m,U,hU,hm,_,hUn,hUl,hUm⟩ := master_sound_support S n row hr.1
    have he := Rep_unique S n row.1 m _ hm hr.2
    subst m
    exact ⟨U,hU,hUn,hUl,hUm⟩
  · intro other ho
    exact hu other ⟨ho.1,ho.2.1⟩

def decodedMasters (S : OddScale) (n : ℕ) : List (MasterEvent (P S n)) :=
  (Rows S n).attach.map (decodeRow S n)

theorem decoded_master_list (S : OddScale) (n : ℕ) :
    (decodedMasters S n).Nodup ∧ (decodedMasters S n).toFinset=Finset.univ := by
  constructor
  · exact (master_nodup S n).1.attach.map (masterEquiv S n).injective
  · apply Finset.eq_univ_of_forall
    intro m
    let row := (masterEquiv S n).symm m
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨row,List.mem_attach _ _,(masterEquiv S n).apply_symm_apply m⟩

/-- Filter the actual decoded masters by the SAME original Eligible. -/
def originalEventSet (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    Finset (Event (P S n) J r) :=
  (((decodedMasters S n).toFinset.filter (fun m => Eligible (P S n) J r m.val)).attach).image
    (fun m => (⟨m.val.val,by
      have hm := m.property
      simp only [Finset.mem_filter] at hm
      exact hm.2⟩ : Event (P S n) J r))

/-- Proof-only original-key sorting; no executable/paid old-rank claim. -/
def originalOrderedEvents (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    List (Event (P S n) J r) :=
  (originalEventSet S n J r).sort (eventPriorityLE (P S n) J r)

theorem original_ordered_exact (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    originalOrderedEvents S n J r=
      (Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r) := by
  have he : originalEventSet S n J r=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    let m := eventToMaster (P S n) J r e
    have hm : m∈(decodedMasters S n).toFinset := by rw [(decoded_master_list S n).2]; simp
    have hf : m∈(decodedMasters S n).toFinset.filter (fun m => Eligible (P S n) J r m.val) :=
      Finset.mem_filter.mpr ⟨hm,e.property⟩
    change e∈originalEventSet S n J r
    unfold originalEventSet
    refine Finset.mem_image.mpr ⟨⟨m,hf⟩,Finset.mem_attach _ _,?_⟩
    exact Subtype.ext rfl
  rw [originalOrderedEvents,he]

theorem original_firstBad (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (z : Vertex (P S n) → Space) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r) z=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r)) z := by
  rw [original_ordered_exact]

theorem original_firstBad_table (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : BDL26NativeStateRows.Samples (Vertex (P S n))) (m : ℕ) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r)
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m))=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r))
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m)) :=
  original_firstBad S n J r lambda K _

theorem candidate_invalid_padding (S : OddScale) (n : ℕ) (a b c d : Code) (ha : a.l≠0) :
    (candidateQ S n a b c d).value=(pack a b c d,none) := by
  have hn : a∉actualCodes S n := by
    intro h
    obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n a).mp h
    exact ha (congrArg (fun c : Code => c.l) ht).symm
  have hr : (BDL26NativeSupportMetadata.atlasReadQ a
      (BDL26NativeSupportMetadata.atlasQ S n).value).value=none := by
    rw [BDL26NativeSupportMetadata.atlas_value]
    exact (BDL26NativeSupportMetadata.atlas_read_missing _ a (actualCodes S n) hn).1
  rw [(candidate_spec S n a b c d).1]
  simp [BDL26NativeSupportMetadata.queryQ,pack,hr]

/-- The only hypotheses are local callback bounds; the closed top-level theorem
below derives them from the actual complete query, never from a caller budget. -/
theorem master_binomial_cost (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    let N := (actualCodes S n).length
    (masterCandidatesQ S n).operations≤A+
      Nat.choose N 4*(A+178*B^2+222*B+509)+
        4*(N+Nat.choose N 2+Nat.choose N 3)+1+N+Nat.choose N 2+2 ∧
      (masterCandidatesQ S n).allocations≤A+
        Nat.choose N 4*(A+4*B^2+8*B+36)+N+Nat.choose N 2+Nat.choose N 3+1 := by
  let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
  let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
  let p := A+178*B^2+222*B+400
  let q := A+4*B^2+8*B+26
  have hf (a b c d : Code) : (candidateQ S n a b c d).operations≤p+100 ∧
      (candidateQ S n a b c d).allocations≤q+6 := by
    have hq := BDL26NativeSupportMetadata.query_polynomial S n (pack a b c d)
    rw [(candidate_spec S n a b c d).2.1,(candidate_spec S n a b c d).2.2]
    exact ⟨Nat.add_le_add_right hq.1 100,Nat.add_le_add_right hq.2 6⟩
  have he := quadruples_bound (candidateQ S n) (actualCodes S n) (p+100) (q+6) hf
  have hs := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hs
  have ha := BDL26NativePresentationGenerator.allocated_polynomial S n
  rw [(master_accounting S n).1,(master_accounting S n).2]
  dsimp only
  constructor <;> dsimp only [p,q,A,B] at * <;> nlinarith [he.2.1,he.2.2]

/-- Closed cost of the actual complete interpreter, including repeated setup
at all choose(N,4) leaves and all three append copies per emitted row. -/
theorem master_polynomial (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (masterCandidatesQ S n).operations≤
      A+(B+1)^4*(A+178*B^2+222*B+509)+13*(B+1)^3+2 ∧
      (masterCandidatesQ S n).allocations≤
        A+(B+1)^4*(A+4*B^2+8*B+36)+3*(B+1)^3+1 := by
  let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
  let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
  let N := (actualCodes S n).length
  let M := B+1
  have hNB : N≤B := BDL26NativeTriangleKeys.triangle_count_bound S n
  have hNM : N≤M := by dsimp only [M]; omega
  have hm : 1≤M := by dsimp only [M]; omega
  have hm2 : M≤M^2 := by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left M hm
  have hm3 : M^2≤M^3 := by nlinarith [Nat.mul_le_mul_left (M*M) hm]
  have h2 : Nat.choose N 2≤M^3 := calc
    Nat.choose N 2≤N^2 := Nat.choose_le_pow _ _
    _≤M^2 := by gcongr
    _≤M^3 := hm3
  have h3 : Nat.choose N 3≤M^3 := (Nat.choose_le_pow N 3).trans (by gcongr)
  have h4 : Nat.choose N 4≤M^4 := (Nat.choose_le_pow N 4).trans (by gcongr)
  have hK : N+Nat.choose N 2+Nat.choose N 3≤3*M^3 := by nlinarith
  have hE : 1+N+Nat.choose N 2≤M^3 := by
    have hh := Nat.choose_le_pow N 2
    have he : 1+N+Nat.choose N 2≤(N+1)^2 := by nlinarith
    have hn : (N+1)^2≤M^2 := by dsimp only [M]; gcongr
    exact he.trans (hn.trans hm3)
  have hc : (masterCandidatesQ S n).operations≤A+
      Nat.choose N 4*(A+178*B^2+222*B+509)+
        4*(N+Nat.choose N 2+Nat.choose N 3)+1+N+Nat.choose N 2+2 ∧
      (masterCandidatesQ S n).allocations≤A+
        Nat.choose N 4*(A+4*B^2+8*B+36)+N+Nat.choose N 2+Nat.choose N 3+1 :=
    master_binomial_cost S n
  change (masterCandidatesQ S n).operations≤A+M^4*(A+178*B^2+222*B+509)+13*M^3+2 ∧
    (masterCandidatesQ S n).allocations≤A+M^4*(A+4*B^2+8*B+36)+3*M^3+1
  have ho := Nat.mul_le_mul_right (A+178*B^2+222*B+509) h4
  have ha := Nat.mul_le_mul_right (A+4*B^2+8*B+36) h4
  constructor <;> omega

end

end QEC.Coding.BDL26NativeMasterCandidates
