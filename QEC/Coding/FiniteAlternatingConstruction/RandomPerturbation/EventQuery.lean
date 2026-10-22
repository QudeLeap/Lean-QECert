import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExactRealProgram
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events

/-! # Actual finite-grid bad-event queries and their counted triangle tests -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set

/-- Evaluate all tests, with one Boolean bookkeeping operation per list entry. -/
def listAllQuery {A : Type*} (q : A → Bool × ℕ) : List A → Bool × ℕ
  | [] => (true,0)
  | a::L => let qa := q a; let rest := listAllQuery q L
            (qa.1 && rest.1,qa.2+rest.2+1)

def listAnyQuery {A : Type*} (q : A → Bool × ℕ) : List A → Bool × ℕ
  | [] => (false,0)
  | a::L => let qa := q a; let rest := listAnyQuery q L
            (qa.1 || rest.1,qa.2+rest.2+1)

theorem listAllQuery_correct {A : Type*} (q : A → Bool × ℕ) (L : List A) :
    (listAllQuery q L).1 = true ↔ ∀ a ∈ L, (q a).1 = true := by
  induction L with
  | nil => simp [listAllQuery]
  | cons a L ih => simp [listAllQuery,ih]

theorem listAnyQuery_correct {A : Type*} (q : A → Bool × ℕ) (L : List A) :
    (listAnyQuery q L).1 = true ↔ ∃ a ∈ L, (q a).1 = true := by
  induction L with
  | nil => simp [listAnyQuery]
  | cons a L ih => simp [listAnyQuery,ih]

theorem listAllQuery_cost_le {A : Type*} (q : A → Bool × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (listAllQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [listAllQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [listAllQuery,List.length_cons]
    nlinarith

theorem listAnyQuery_cost_le {A : Type*} (q : A → Bool × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (listAnyQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [listAnyQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [listAnyQuery,List.length_cons]
    nlinarith

noncomputable def eventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) : Bool × ℕ :=
  listAnyQuery (fun g : Grid K =>
    listAllQuery (fun a : e.val =>
      triangleQuery (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+
        p (eventVertex P J radius e a i)) (eventCenter P J radius lambda K e g) 2)
      (Finset.univ.toList : List e.val))
    (Finset.univ.toList : List (Grid K))

theorem eventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) :
    (eventQuery P J radius lambda K e p).1 = true ↔ p ∈ eventBad P J radius lambda K e := by
  simp only [eventQuery,listAnyQuery_correct,listAllQuery_correct,Finset.mem_toList,
    Finset.mem_univ,true_and,eventBad,Set.mem_iUnion,Set.mem_iInter,Set.mem_preimage]
  simp only [triangleQuery_correct _ _ (by norm_num : (0 : ℝ) ≤ 2),
    triangleHit,Set.mem_setOf_eq,true_implies]

/-- The fixed event uses four labeled triangles at each of its fixed grid centers. -/
theorem eventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) :
    (eventQuery P J radius lambda K e p).2 ≤ Fintype.card (Grid K)*(4*200001+1) := by
  have hc (g : Grid K) :
      (listAllQuery (fun a : e.val =>
        triangleQuery (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+
          p (eventVertex P J radius e a i)) (eventCenter P J radius lambda K e g) 2)
        (Finset.univ.toList : List e.val)).2 ≤ 4*200001 := by
    have h := listAllQuery_cost_le (fun a : e.val =>
      triangleQuery (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+
        p (eventVertex P J radius e a i)) (eventCenter P J radius lambda K e g) 2)
      (Finset.univ.toList : List e.val) 200000 (fun a _ => triangleQuery_cost_le _ _ _)
    simpa only [Finset.length_toList,Finset.card_univ,Fintype.card_coe,e.property.1] using h
  have h := listAnyQuery_cost_le (fun g : Grid K =>
    listAllQuery (fun a : e.val =>
      triangleQuery (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+
        p (eventVertex P J radius e a i)) (eventCenter P J radius lambda K e g) 2)
      (Finset.univ.toList : List e.val))
    (Finset.univ.toList : List (Grid K)) (4*200001) (fun g _ => hc g)
  simpa only [eventQuery,Finset.length_toList,Finset.card_univ] using h

end QEC.Coding.BDL26RandomPerturbation
