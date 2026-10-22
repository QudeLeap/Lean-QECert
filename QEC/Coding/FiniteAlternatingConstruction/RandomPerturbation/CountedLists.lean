import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Counted input index lookup and finite ordered-list preparation -/
namespace QEC.Coding.BDL26RandomPerturbation

/-- Linear input-array lookup charges each tested label. Missing labels return length. -/
def indexQuery {A : Type*} [DecidableEq A] (a : A) : List A → ℕ × ℕ
  | [] => (0,0)
  | b::L => if b = a then (0,1) else
      let q := indexQuery a L
      (q.1+1,q.2+1)

theorem indexQuery_value {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A] (a : A) (L : List A) :
    (indexQuery a L).1 = L.idxOf a := by
  induction L with
  | nil => simp [indexQuery]
  | cons b L ih =>
    by_cases h : b = a
    · simp [indexQuery,h]
    · simp [indexQuery,h,List.idxOf_cons_ne L h,ih]

theorem indexQuery_cost_le {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (indexQuery a L).2 ≤ L.length := by
  induction L with
  | nil => simp [indexQuery]
  | cons b L ih =>
    by_cases h : b = a <;> simp only [indexQuery,h,if_true,if_false,List.length_cons] <;> omega

/-- Insertion with the actual counted comparator, including list bookkeeping. -/
def orderedInsertQuery {A : Type*} (cmp : A → A → Bool × ℕ) (a : A) : List A → List A × ℕ
  | [] => ([a],1)
  | b::L =>
      let c := cmp a b
      if c.1 then (a::b::L,c.2+1) else
        let q := orderedInsertQuery cmp a L
        (b::q.1,c.2+q.2+1)

def sortQuery {A : Type*} (cmp : A → A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],0)
  | a::L =>
      let q := sortQuery cmp L
      let ins := orderedInsertQuery cmp a q.1
      (ins.1,q.2+ins.2)

theorem orderedInsertQuery_value {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).1 = L.orderedInsert r a := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : r a b
    · have hb : (cmp a b).1 = true := (hc a b).mpr h
      simp [orderedInsertQuery,List.orderedInsert,h,hb]
    · have hb : (cmp a b).1 = false := Bool.eq_false_iff.mpr (fun ht => h ((hc a b).mp ht))
      simp [orderedInsertQuery,List.orderedInsert,h,hb,ih]

theorem sortQuery_value {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (L : List A) :
    (sortQuery cmp L).1 = L.insertionSort r := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [sortQuery,List.insertionSort_cons]
    rw [orderedInsertQuery_value cmp r hc,ih]

theorem orderedInsertQuery_cost_le {A : Type*} (cmp : A → A → Bool × ℕ) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).2 ≤ (L.length+1)*(C+1) := by
  induction L with
  | nil => simp [orderedInsertQuery]
  | cons b L ih =>
    have hb := hc a b
    simp only [orderedInsertQuery,List.length_cons]
    split_ifs <;> simp only [Prod.snd]
    all_goals nlinarith

theorem sortQuery_cost_le {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hv : ∀ a b, (cmp a b).1 = true ↔ r a b) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (L : List A) :
    (sortQuery cmp L).2 ≤ (L.length+1)^2*(C+1) := by
  induction L with
  | nil => simp [sortQuery]
  | cons a L ih =>
    have hi := orderedInsertQuery_cost_le cmp C hc a (sortQuery cmp L).1
    have hlen : ((sortQuery cmp L).1).length = L.length := by
      rw [sortQuery_value cmp r hv,List.length_insertionSort]
    rw [hlen] at hi
    simp only [sortQuery,List.length_cons]
    nlinarith

end QEC.Coding.BDL26RandomPerturbation
