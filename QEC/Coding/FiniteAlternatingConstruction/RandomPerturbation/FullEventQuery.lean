import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.AnchorQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GridEnumerationQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.SnapshotQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventQuery

/-! # Full bad-event queries include anchor selection, grid loops and coordinate arithmetic -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def fullCenterQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) : Space × ℕ :=
  match a with
  | none => (0,1)
  | some t => let grid := gridPointQuery K g
              let point := pointSnapshotQuery lambda (J (.x (P.faceX t.1))) grid.1
              (point.1,grid.2+point.2+2)

theorem fullCenterQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g).1 =
      eventCenter P J r lambda K e g := by
  rw [eventAnchorQuery_value]
  simp only [fullCenterQuery,pointSnapshotQuery_value,gridPointQuery_value]
  rfl

theorem fullCenterQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) :
    (fullCenterQuery P J lambda K a g).2 ≤ 3*K+56 := by
  cases a with
  | none => simp [fullCenterQuery]
  | some t =>
    have hg := gridPointQuery_cost_le K g
    have hp := pointSnapshotQuery_cost_le lambda (J (.x (P.faceX t.1))) (gridPointQuery K g).1
    dsimp only [fullCenterQuery]
    omega

noncomputable def fullTriangleQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) (center : Space) : Bool × ℕ :=
  let snapshot := triangleSnapshotQuery P J r lambda e a p
  let query := triangleQuery snapshot.1 center 2
  (query.1,snapshot.2+query.2+15)

theorem fullTriangleQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) (center : Space) :
    (fullTriangleQuery P J r lambda e a p center).1 = true ↔
      (fun i => p (eventVertex P J r e a i)) ∈
        triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))) center 2 := by
  simp only [fullTriangleQuery,triangleSnapshotQuery_value,
    triangleQuery_correct _ _ (by norm_num : (0 : ℝ) ≤ 2),triangleHit,Set.mem_setOf_eq]

theorem fullTriangleQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) (center : Space) :
    (fullTriangleQuery P J r lambda e a p center).2 ≤ 200200 := by
  have hs := triangleSnapshotQuery_cost_le P J r lambda e a p
  have hq := triangleQuery_cost_le (triangleSnapshotQuery P J r lambda e a p).1 center 2
  dsimp only [fullTriangleQuery]
  omega

noncomputable def fullEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r)
    (p : eventSupport P J r e → Space) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P J r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      fullTriangleQuery P J r lambda e a p center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)

theorem fullEventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : eventSupport P J r e → Space) :
    (fullEventQuery P J r lambda K e p).1 = true ↔ p ∈ eventBad P J r lambda K e := by
  simp only [fullEventQuery,listAnyQuery_correct,listAllQuery_correct,Finset.mem_toList,
    Finset.mem_univ,true_and,fullTriangleQuery_correct,fullCenterQuery_value,
    eventBad,Set.mem_iUnion,Set.mem_iInter,Set.mem_preimage,true_implies]
  constructor
  · rintro ⟨g,hg,h⟩; exact ⟨g,h⟩
  · rintro ⟨g,h⟩; exact ⟨g,gridListQuery_complete K g,h⟩

def fullQueryBudget (n K : ℕ) : ℕ :=
  6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1+8*n+10+
    (2*K+1)^3*(3*K+65+4*200201)

theorem fullEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : eventSupport P J r e → Space) :
    (fullEventQuery P J r lambda K e p).2 ≤ fullQueryBudget (Fintype.card (Triangle P)) K := by
  have hg := gridListQuery_cost_le K
  have ha := eventAnchorQuery_cost_le P J r e
  have hq := listAnyQuery_cost_le (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g
    let triangles := listAllQuery (fun a : e.val =>
      fullTriangleQuery P J r lambda e a p center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) (gridListQuery K).1 (3*K+64+4*200201) (by
      intro g hg
      have hc := fullCenterQuery_cost_le P J lambda K (eventAnchorQuery P J r e).1 g
      have ht := listAllQuery_cost_le (fun a : e.val => fullTriangleQuery P J r lambda e a p
        (fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g).1)
        (Finset.univ.toList : List e.val) 200200 (fun a _ => fullTriangleQuery_cost_le P J r lambda e a p _)
      simp only [Finset.length_toList,Finset.card_univ,Fintype.card_coe,e.property.1] at ht
      dsimp only
      omega)
  rw [gridListQuery_length] at hq
  dsimp only at hq
  dsimp only [fullEventQuery,fullQueryBudget]
  norm_num only [Nat.add_assoc] at hq ⊢
  omega

end QEC.Coding.BDL26RandomPerturbation
