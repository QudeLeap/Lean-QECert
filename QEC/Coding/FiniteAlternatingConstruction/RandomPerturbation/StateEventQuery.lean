import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.StateRows
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FullEventQuery

/-! # Geometric event queries consume and charge the explicit current row array -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def stateTrianglePointsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) : (Fin 3 → Space) × ℕ :=
  let r0 := stateRowQuery (triangleVertex P t 0) R
  let r1 := stateRowQuery (triangleVertex P t 1) R
  let r2 := stateRowQuery (triangleVertex P t 2) R
  let q0 := pointSnapshotQuery lambda (J (triangleVertex P t 0)) r0.1.2
  let q1 := pointSnapshotQuery lambda (J (triangleVertex P t 1)) r1.1.2
  let q2 := pointSnapshotQuery lambda (J (triangleVertex P t 2)) r2.1.2
  (![q0.1,q1.1,q2.1],r0.2+r1.2+r2.2+q0.2+q1.2+q2.2+18)

theorem stateTrianglePointsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (stateTrianglePointsQuery P J lambda t R).1 =
      fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P t i))+statePoints R (triangleVertex P t i) := by
  funext i
  fin_cases i <;> simp [stateTrianglePointsQuery,pointSnapshotQuery_value,statePoints]

theorem stateTrianglePointsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (stateTrianglePointsQuery P J lambda t R).2 ≤ 153+6*R.length := by
  have h0 := stateRowQuery_cost_le (triangleVertex P t 0) R
  have h1 := stateRowQuery_cost_le (triangleVertex P t 1) R
  have h2 := stateRowQuery_cost_le (triangleVertex P t 2) R
  have q0 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P t 0)) (stateRowQuery (triangleVertex P t 0) R).1.2
  have q1 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P t 1)) (stateRowQuery (triangleVertex P t 1) R).1.2
  have q2 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P t 2)) (stateRowQuery (triangleVertex P t 2) R).1.2
  dsimp only [stateTrianglePointsQuery]
  omega

noncomputable def stateTriangleQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) : Bool × ℕ :=
  let points := stateTrianglePointsQuery P J lambda t R
  let query := triangleQuery points.1 z 2
  (query.1,points.2+query.2)

theorem stateTriangleQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (stateTriangleQuery P J lambda t R z).1 = true ↔
      (fun i => statePoints R (triangleVertex P t i)) ∈
        triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P t i))) z 2 := by
  simp only [stateTriangleQuery,stateTrianglePointsQuery_value,
    triangleQuery_correct _ _ (by norm_num : (0 : ℝ) ≤ 2),triangleHit,Set.mem_setOf_eq]

theorem stateTriangleQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (stateTriangleQuery P J lambda t R z).2 ≤ 200200+6*R.length := by
  have hp := stateTrianglePointsQuery_cost_le P J lambda t R
  have hq := triangleQuery_cost_le (stateTrianglePointsQuery P J lambda t R).1 z 2
  dsimp only [stateTriangleQuery]
  omega

noncomputable def stateEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P J r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P J lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)

theorem stateEventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    (stateEventQuery P J r lambda K e R).1 = true ↔
      statePoints R ∈ localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r lambda K) e := by
  rw [mem_global_event]
  simp only [stateEventQuery,listAnyQuery_correct,listAllQuery_correct,Finset.mem_toList,
    Finset.mem_univ,stateTriangleQuery_correct,fullCenterQuery_value,true_implies]
  constructor
  · rintro ⟨g,hg,h⟩; exact ⟨g,h⟩
  · rintro ⟨g,h⟩; exact ⟨g,gridListQuery_complete K g,h⟩

def stateQueryBudget (n v K : ℕ) : ℕ := fullQueryBudget n K+24*(2*K+1)^3*v

theorem stateEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    (stateEventQuery P J r lambda K e R).2 ≤ stateQueryBudget (Fintype.card (Triangle P)) R.length K := by
  have hg := gridListQuery_cost_le K
  have ha := eventAnchorQuery_cost_le P J r e
  have hq := listAnyQuery_cost_le (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P J lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) (gridListQuery K).1 (3*K+64+4*(200201+6*R.length)) (by
      intro g hg
      have hc := fullCenterQuery_cost_le P J lambda K (eventAnchorQuery P J r e).1 g
      have ht := listAllQuery_cost_le (fun a : e.val => stateTriangleQuery P J lambda a.val R
        (fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g).1)
        (Finset.univ.toList : List e.val) (200200+6*R.length) (fun a _ => stateTriangleQuery_cost_le P J lambda a.val R _)
      simp only [Finset.length_toList,Finset.card_univ,Fintype.card_coe,e.property.1] at ht
      dsimp only
      omega)
  rw [gridListQuery_length] at hq
  dsimp only at hq
  dsimp only [stateEventQuery,stateQueryBudget,fullQueryBudget]
  nlinarith

end QEC.Coding.BDL26RandomPerturbation
