import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FourTupleEnumeration
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedFilterMap

/-! # Counted nested input loops construct the actual four-label candidate list -/
namespace QEC.Coding.BDL26RandomPerturbation

def flatMapQuery {A B : Type*} (q : A → List B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let tail := flatMapQuery q L
            (qa.1++tail.1,qa.2+tail.2+qa.1.length+1)

theorem flatMapQuery_value {A B : Type*} (q : A → List B × ℕ) (L : List A) :
    (flatMapQuery q L).1 = L.flatMap (fun a => (q a).1) := by
  induction L <;> simp_all [flatMapQuery]

theorem flatMapQuery_cost_le {A T : Type*} (q : A → List T × ℕ) (L : List A) (maxLength maxCost : ℕ)
    (hlen : ∀ a ∈ L, (q a).1.length ≤ maxLength) (hcost : ∀ a ∈ L, (q a).2 ≤ maxCost) :
    (flatMapQuery q L).2 ≤ L.length*(maxLength+maxCost+1) := by
  induction L with
  | nil => simp [flatMapQuery]
  | cons a L ih =>
    have ha := hlen a (by simp)
    have hc := hcost a (by simp)
    have ht := ih (fun b hb => hlen b (by simp [hb])) (fun b hb => hcost b (by simp [hb]))
    simp only [flatMapQuery,List.length_cons]
    nlinarith

def fourTuple1Query {A : Type*} (L : List A) (a b c : A) : List (List A) × ℕ :=
  flatMapQuery (fun d => ([[a,b,c,d]],8)) L

def fourTuple2Query {A : Type*} (L : List A) (a b : A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple1Query L a b) L

def fourTuple3Query {A : Type*} (L : List A) (a : A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple2Query L a) L

def fourTuplesQuery {A : Type*} (L : List A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple3Query L) L

theorem fourTuple1Query_value {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).1 = L.map (fun d => [a,b,c,d]) := by
  simp only [fourTuple1Query,flatMapQuery_value,← List.map_eq_flatMap]

theorem fourTuple1Query_length {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).1.length = L.length := by
  rw [fourTuple1Query_value,List.length_map]

theorem fourTuple2Query_length {A : Type*} (L : List A) (a b : A) :
    (fourTuple2Query L a b).1.length = L.length^2 := by
  rw [fourTuple2Query,flatMapQuery_value,flatMap_length_of_const L _ L.length
    (fun c _ => fourTuple1Query_length L a b c)]
  ring

theorem fourTuple3Query_length {A : Type*} (L : List A) (a : A) :
    (fourTuple3Query L a).1.length = L.length^3 := by
  rw [fourTuple3Query,flatMapQuery_value,flatMap_length_of_const L _ (L.length^2)
    (fun b _ => fourTuple2Query_length L a b)]
  ring

theorem fourTuplesQuery_value {A : Type*} (L : List A) : (fourTuplesQuery L).1 = fourTuples L := by
  simp only [fourTuplesQuery,fourTuple3Query,fourTuple2Query,flatMapQuery_value,
    fourTuple1Query_value,fourTuples]

theorem fourTuple1Query_cost_le {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).2 ≤ 10*L.length := by
  have h := flatMapQuery_cost_le (fun d => ([[a,b,c,d]],8)) L 1 8
    (by intro d hd; simp) (by intro d hd; exact le_rfl)
  norm_num only at h
  simpa only [fourTuple1Query,Nat.mul_comm] using h

theorem fourTuple2Query_cost_le {A : Type*} (L : List A) (a b : A) :
    (fourTuple2Query L a b).2 ≤ 11*L.length^2+L.length := by
  have h := flatMapQuery_cost_le (fourTuple1Query L a b) L L.length (10*L.length)
    (fun c _ => (fourTuple1Query_length L a b c).le) (fun c _ => fourTuple1Query_cost_le L a b c)
  dsimp only [fourTuple2Query]
  nlinarith

theorem fourTuple3Query_cost_le {A : Type*} (L : List A) (a : A) :
    (fourTuple3Query L a).2 ≤ 12*L.length^3+L.length^2+L.length := by
  have h := flatMapQuery_cost_le (fourTuple2Query L a) L (L.length^2)
    (11*L.length^2+L.length)
    (fun b _ => (fourTuple2Query_length L a b).le) (fun b _ => fourTuple2Query_cost_le L a b)
  dsimp only [fourTuple3Query]
  nlinarith

theorem fourTuplesQuery_cost_le {A : Type*} (L : List A) :
    (fourTuplesQuery L).2 ≤ 13*L.length^4+L.length^3+L.length^2+L.length := by
  have h := flatMapQuery_cost_le (fourTuple3Query L) L (L.length^3)
    (12*L.length^3+L.length^2+L.length)
    (fun a _ => (fourTuple3Query_length L a).le) (fun a _ => fourTuple3Query_cost_le L a)
  dsimp only [fourTuplesQuery]
  nlinarith

end QEC.Coding.BDL26RandomPerturbation
