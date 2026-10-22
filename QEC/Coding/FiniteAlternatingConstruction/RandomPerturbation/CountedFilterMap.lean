import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedDedup

/-! # Actual finite candidate filtering with counted query operations -/
namespace QEC.Coding.BDL26RandomPerturbation

def filterMapQuery {A B : Type*} (q : A → Option B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let tail := filterMapQuery q L
            ((match qa.1 with | none => tail.1 | some b => b::tail.1),qa.2+tail.2+1)

theorem filterMapQuery_value {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1 = L.filterMap (fun a => (q a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases he : (q a).1 <;> simp [filterMapQuery,he,ih]

theorem filterMapQuery_length_le {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1.length ≤ L.length := by
  rw [filterMapQuery_value]
  exact List.length_filterMap_le _ _

theorem filterMapQuery_cost_le {A B : Type*} (q : A → Option B × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (filterMapQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [filterMapQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [filterMapQuery,List.length_cons]
    nlinarith

end QEC.Coding.BDL26RandomPerturbation
