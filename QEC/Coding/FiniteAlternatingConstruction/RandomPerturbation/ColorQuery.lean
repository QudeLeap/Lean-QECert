import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventKeyQuery

/-! # Counted incidence ranks computed from the actual triangle input list -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

/-- Count successful finite tests and the operations actually used by them. -/
def countQuery {A : Type*} (q : A → Bool × ℕ) : List A → ℕ × ℕ
  | [] => (0,0)
  | a::L => let qa := q a; let tail := countQuery q L
            ((if qa.1 then 1 else 0)+tail.1,qa.2+tail.2+1)

theorem countQuery_value {A : Type*} (q : A → Bool × ℕ) (L : List A) :
    (countQuery q L).1 = L.countP (fun a => (q a).1) := by
  induction L <;> simp_all [countQuery,List.countP_cons,Nat.add_comm]

theorem countQuery_cost_le {A : Type*} (q : A → Bool × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (countQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [countQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [countQuery,List.length_cons]
    nlinarith

noncomputable def fiberRankQuery (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) : ℕ × ℕ :=
  let rankA := indexQuery a (triangleInputList P)
  let q := countQuery (fun b : Triangle P =>
    let rankB := indexQuery b (triangleInputList P)
    (decide (f b = f a ∧ rankB.1 < rankA.1),rankB.2+4)) (triangleInputList P)
  (q.1,rankA.2+q.2)

/-- Both ranks are derived by finite input lookup; two owner reads and both comparisons are counted. -/
theorem fiberRankQuery_cost_le (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) :
    (fiberRankQuery P f a).2 ≤ Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6) := by
  have ha := indexQuery_cost_le a (triangleInputList P)
  rw [triangleInputList_length] at ha
  have hc := countQuery_cost_le (fun b : Triangle P =>
    let rankB := indexQuery b (triangleInputList P)
    (decide (f b = f a ∧ rankB.1 < (indexQuery a (triangleInputList P)).1),rankB.2+4))
    (triangleInputList P) (Fintype.card (Triangle P)+4) (by
      intro b _
      have h := indexQuery_cost_le b (triangleInputList P)
      simpa only [triangleInputList_length,Nat.add_le_add_iff_right] using h)
  rw [triangleInputList_length] at hc
  dsimp only [fiberRankQuery]
  nlinarith

-- Equality with fiberRank is obtained by the input-list membership/nodup proof
-- and finite filter-card / countP equality, rather than a caller rank certificate.


theorem triangleInputList_toFinset (P : TannerSquarePresentation) :
    (triangleInputList P).toFinset = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro t
  apply List.mem_toFinset.mpr
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin (Triangle P) t,(Fintype.equivFin (Triangle P)).symm_apply_apply t⟩

theorem fiberRankQuery_value (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) :
    (fiberRankQuery P f a).1 = fiberRank (triangleKey P) f a := by
  classical
  have hn : (triangleInputList P).Nodup :=
    List.nodup_ofFn_ofInjective (Fintype.equivFin (Triangle P)).symm.injective
  simp only [fiberRankQuery,countQuery_value,indexQuery_value,triangleInputList_index]
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hn.filter _),List.toFinset_filter,triangleInputList_toFinset]
  simp only [decide_eq_true_eq]
  rfl

noncomputable def triangleColorQuery (P : TannerSquarePresentation) (a : Triangle P) :
    (Fin 3 → ℕ) × ℕ := by
  classical
  let qx := fiberRankQuery P (fun t => P.faceX t.1) a
  let qq := fiberRankQuery P (fun t => P.faceQ t.1 t.2) a
  let qz := fiberRankQuery P (fun t => P.faceZ t.1) a
  exact (![qx.1,qq.1,qz.1],qx.2+qq.2+qz.2)

theorem triangleColorQuery_value (P : TannerSquarePresentation) (a : Triangle P) :
    (triangleColorQuery P a).1 = triangleColor P a := by
  classical
  funext i
  fin_cases i <;> simp [triangleColorQuery,triangleColor,fiberRankQuery_value]

theorem triangleColorQuery_cost_le (P : TannerSquarePresentation) (a : Triangle P) :
    (triangleColorQuery P a).2 ≤ 3*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6) := by
  classical
  have hx := fiberRankQuery_cost_le P (fun t => P.faceX t.1) a
  have hq := fiberRankQuery_cost_le P (fun t => P.faceQ t.1 t.2) a
  have hz := fiberRankQuery_cost_le P (fun t => P.faceZ t.1) a
  dsimp only [triangleColorQuery]
  nlinarith

end QEC.Coding.BDL26RandomPerturbation
