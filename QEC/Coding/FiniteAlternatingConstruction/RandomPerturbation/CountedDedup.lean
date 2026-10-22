import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedLists
import Mathlib.Data.List.Dedup

/-! # Counted duplicate elimination uses actual finite label equality queries -/
namespace QEC.Coding.BDL26RandomPerturbation

def memberQuery {A : Type*} (eq : A → A → Bool × ℕ) (a : A) : List A → Bool × ℕ
  | [] => (false,0)
  | b::L => let qb := eq a b
            if qb.1 then (true,qb.2+1) else
              let tail := memberQuery eq a L
              (tail.1,qb.2+tail.2+1)

theorem memberQuery_correct {A : Type*} (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (a : A) (L : List A) :
    (memberQuery eq a L).1 = true ↔ a ∈ L := by
  induction L with
  | nil => simp [memberQuery]
  | cons b L ih =>
    by_cases h : a = b
    · subst b
      have hb := (heq a a).mpr rfl
      simp [memberQuery,hb]
    · have hb : (eq a b).1 = false := Bool.eq_false_iff.mpr (fun ht => h ((heq a b).mp ht))
      simp [memberQuery,h,hb,ih]

theorem memberQuery_cost_le {A : Type*} (eq : A → A → Bool × ℕ) (C : ℕ)
    (h : ∀ a b, (eq a b).2 ≤ C) (a : A) (L : List A) :
    (memberQuery eq a L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [memberQuery]
  | cons b L ih =>
    have hb := h a b
    simp only [memberQuery,List.length_cons]
    split_ifs <;> nlinarith

def dedupQuery {A : Type*} (eq : A → A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],0)
  | a::L => let tail := dedupQuery eq L
            let q := memberQuery eq a tail.1
            (if q.1 then tail.1 else a::tail.1,tail.2+q.2+1)

theorem dedupQuery_value {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (L : List A) :
    (dedupQuery eq L).1 = L.dedup := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have h : (memberQuery eq a (dedupQuery eq L).1).1 = true ↔ a ∈ L := by
      rw [memberQuery_correct eq heq,ih,List.mem_dedup]
    by_cases ha : a ∈ L
    · have hq := h.mpr ha
      simp only [dedupQuery]
      rw [if_pos hq]
      simpa only [List.dedup_cons_of_mem ha] using ih
    · have hq : (memberQuery eq a (dedupQuery eq L).1).1 = false :=
        Bool.eq_false_iff.mpr (fun ht => ha (h.mp ht))
      have hn : (memberQuery eq a (dedupQuery eq L).1).1 ≠ true := by rw [hq]; decide
      simp only [dedupQuery]
      rw [if_neg hn]
      simpa only [List.dedup_cons_of_notMem ha] using congrArg (List.cons a) ih

theorem dedupQuery_cost_le {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (C : ℕ)
    (hc : ∀ a b, (eq a b).2 ≤ C) (L : List A) :
    (dedupQuery eq L).2 ≤ (L.length+1)^2*(C+1) := by
  induction L with
  | nil => simp [dedupQuery]
  | cons a L ih =>
    have hm := memberQuery_cost_le eq C hc a (dedupQuery eq L).1
    have hlen : (dedupQuery eq L).1.length ≤ L.length := by
      rw [dedupQuery_value eq heq]
      exact (List.dedup_sublist L).length_le
    have hm' : (memberQuery eq a (dedupQuery eq L).1).2 ≤ L.length*(C+1) :=
      hm.trans (Nat.mul_le_mul_right _ hlen)
    simp only [dedupQuery,List.length_cons]
    nlinarith

end QEC.Coding.BDL26RandomPerturbation
