import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ColorQuery

/-! # The deterministic event anchor selected by counted input-rank searches -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def lowerTriangleQuery (P : TannerSquarePresentation) (a b : Triangle P) : Triangle P × ℕ :=
  let qa := indexQuery a (triangleInputList P)
  let qb := indexQuery b (triangleInputList P)
  (if qa.1 ≤ qb.1 then a else b,qa.2+qb.2+1)

theorem lowerTriangleQuery_key (P : TannerSquarePresentation) (a b : Triangle P) :
    triangleKey P (lowerTriangleQuery P a b).1 = min (triangleKey P a) (triangleKey P b) := by
  simp only [lowerTriangleQuery,indexQuery_value,triangleInputList_index]
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (by omega)).symm

theorem lowerTriangleQuery_mem (P : TannerSquarePresentation) (a b : Triangle P) :
    (lowerTriangleQuery P a b).1 = a ∨ (lowerTriangleQuery P a b).1 = b := by
  dsimp only [lowerTriangleQuery]
  split_ifs <;> simp

theorem lowerTriangleQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (lowerTriangleQuery P a b).2 ≤ 2*Fintype.card (Triangle P)+1 := by
  have ha := indexQuery_cost_le a (triangleInputList P)
  have hb := indexQuery_cost_le b (triangleInputList P)
  rw [triangleInputList_length] at ha hb
  dsimp only [lowerTriangleQuery]
  omega

noncomputable def anchorFoldQuery (P : TannerSquarePresentation) (a : Triangle P) :
    List (Triangle P) → Triangle P × ℕ
  | [] => (a,0)
  | b::L => let lower := lowerTriangleQuery P a b
            let rest := anchorFoldQuery P lower.1 L
            (rest.1,lower.2+rest.2+1)

theorem anchorFoldQuery_mem (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    (anchorFoldQuery P a L).1 ∈ a::L := by
  induction L generalizing a with
  | nil => simp [anchorFoldQuery]
  | cons b L ih =>
    have hr := ih (lowerTriangleQuery P a b).1
    simp only [List.mem_cons] at hr ⊢
    rcases hr with h|h
    · rcases lowerTriangleQuery_mem P a b with ha|hb
      · exact Or.inl (h.trans ha)
      · exact Or.inr (Or.inl (h.trans hb))
    · exact Or.inr (Or.inr h)

theorem anchorFoldQuery_min (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    ∀ t ∈ a::L, triangleKey P (anchorFoldQuery P a L).1 ≤ triangleKey P t := by
  induction L generalizing a with
  | nil =>
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact le_rfl
  | cons b L ih =>
    have hr := ih (lowerTriangleQuery P a b).1
    have hlow := hr (lowerTriangleQuery P a b).1 (by simp)
    rw [lowerTriangleQuery_key] at hlow
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with h|h|h
    · subst t; exact hlow.trans (min_le_left _ _)
    · subst t; exact hlow.trans (min_le_right _ _)
    · exact hr t (by simp [h])

theorem anchorFoldQuery_cost_le (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    (anchorFoldQuery P a L).2 ≤ L.length*(2*Fintype.card (Triangle P)+2) := by
  induction L generalizing a with
  | nil => simp [anchorFoldQuery]
  | cons b L ih =>
    have hl := lowerTriangleQuery_cost_le P a b
    have hr := ih (lowerTriangleQuery P a b).1
    simp only [anchorFoldQuery,List.length_cons]
    nlinarith

noncomputable def eventAnchorQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : Option (Triangle P) × ℕ :=
  match e.val.toList with
  | [] => (none,1)
  | a::L => let q := anchorFoldQuery P a L
            (some q.1,q.2+1)

theorem eventAnchorQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : (eventAnchorQuery P J r e).1 = some (eventAnchor P J r e) := by
  classical
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  cases he : e.val.toList with
  | nil =>
    have hc : e.val.toList.length = 4 := by simpa using e.property.1
    rw [he] at hc
    contradiction
  | cons a L =>
    have hm : (anchorFoldQuery P a L).1 ∈ e.val := by
      apply Finset.mem_toList.mp
      rw [he]
      exact anchorFoldQuery_mem P a L
    have ha : eventAnchor P J r e ∈ a::L := by
      rw [← he]
      exact Finset.mem_toList.mpr (eventAnchor_mem P J r e)
    have hlo := anchorFoldQuery_min P a L _ ha
    have hhi : triangleKey P (eventAnchor P J r e) ≤ triangleKey P (anchorFoldQuery P a L).1 :=
      Finset.min'_le e.val _ hm
    have heq := triangleKey_injective P (le_antisymm hlo hhi)
    simp only [eventAnchorQuery,he,heq]

theorem eventAnchorQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    (eventAnchorQuery P J r e).2 ≤ 8*Fintype.card (Triangle P)+9 := by
  have hc : e.val.toList.length = 4 := by simpa using e.property.1
  cases he : e.val.toList with
  | nil => simp [eventAnchorQuery,he]
  | cons a L =>
    have hl := anchorFoldQuery_cost_le P a L
    rw [he,List.length_cons] at hc
    simp only [eventAnchorQuery,he]
    nlinarith

end QEC.Coding.BDL26RandomPerturbation
