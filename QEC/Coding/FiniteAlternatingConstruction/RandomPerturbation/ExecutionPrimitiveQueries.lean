import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FullEventQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventUniverse
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExpectedSteps

/-! # Actual initial draws, refreshed rows and emitted perturbation coordinates -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

noncomputable def vertexInputList (P : TannerSquarePresentation) : List (Vertex P) :=
  List.ofFn (Fintype.equivFin (Vertex P)).symm

theorem vertexInputList_length (P : TannerSquarePresentation) :
    (vertexInputList P).length = Fintype.card (Vertex P) := List.length_ofFn

theorem vertexInputList_complete (P : TannerSquarePresentation) (v : Vertex P) :
    v ∈ vertexInputList P :=
  List.mem_ofFn.mpr ⟨Fintype.equivFin _ v,(Fintype.equivFin _).symm_apply_apply v⟩

/-- One continuous draw, zero counter and stored input-label/point pair per input row. -/
noncomputable def initialRowsQuery (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) : List (Vertex P × ℕ × Space) × ℕ :=
  mapQuery (fun v => ((v,0,T (v,0)),4)) (vertexInputList P)

theorem initialRowsQuery_value (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (initialRowsQuery P T).1 = (vertexInputList P).map (fun v => (v,0,T (v,0))) :=
  mapQuery_value _ _

theorem initialRowsQuery_cost_le (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (initialRowsQuery P T).2 ≤ 5*Fintype.card (Vertex P) := by
  simpa only [initialRowsQuery,vertexInputList_length,Nat.mul_comm] using
    mapQuery_cost_le (fun v : Vertex P => ((v,0,T (v,0)),4)) (vertexInputList P) 4 (by intro v hv; exact le_rfl)

noncomputable def supportListQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : List (Vertex P) × ℕ := by
  classical
  let raw := flatMapQuery (fun t : Triangle P =>
    ([triangleVertex P t 0,triangleVertex P t 1,triangleVertex P t 2],6)) e.val.toList
  let unique := dedupQuery (fun v w : Vertex P => (decide (v=w),1)) raw.1
  exact (unique.1,raw.2+unique.2)

/-- Refreshes visit the support extracted from the four actual triangle labels. -/
theorem supportListQuery_mem (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (v : Vertex P) :
    v ∈ (supportListQuery P J r e).1 ↔ v ∈ eventSupport P J r e := by
  classical
  have heq : ∀ a b : Vertex P,
      ((fun v w : Vertex P => (decide (v=w),(1 : ℕ))) a b).1 = true ↔ a = b := by
    intro a b
    simp
  dsimp only [supportListQuery]
  rw [dedupQuery_value (fun v w : Vertex P => (decide (v=w),1)) heq]
  simp only [List.mem_dedup,
    flatMapQuery_value,List.mem_flatMap,Finset.mem_toList,eventSupport,Finset.mem_biUnion,
    triangleSupport,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨t,ht,hv⟩
    simp at hv
    rcases hv with h|h|h
    · exact ⟨t,ht,0,h.symm⟩
    · exact ⟨t,ht,1,h.symm⟩
    · exact ⟨t,ht,2,h.symm⟩
  · rintro ⟨t,ht,i,hi⟩
    refine ⟨t,ht,?_⟩
    fin_cases i <;> simp [← hi]

noncomputable def outputRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun v => let q := pointSnapshotQuery lambda (J v) (p v)
                     ((v,q.1),q.2+3)) (vertexInputList P)

theorem outputRowsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) :
    (outputRowsQuery P J lambda p).1 =
      (vertexInputList P).map (fun v => (v,lambda • ((1/2 : ℝ) • J v)+p v)) := by
  simp only [outputRowsQuery,mapQuery_value,pointSnapshotQuery_value]

theorem outputRowsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) :
    (outputRowsQuery P J lambda p).2 ≤ 49*Fintype.card (Vertex P) := by
  have h := mapQuery_cost_le (fun v : Vertex P => let q := pointSnapshotQuery lambda (J v) (p v)
    ((v,q.1),q.2+3)) (vertexInputList P) 48 (by
      intro v hv
      have hc := pointSnapshotQuery_cost_le lambda (J v) (p v)
      dsimp only
      omega)
  simpa only [outputRowsQuery,vertexInputList_length,Nat.mul_comm] using h

theorem supportListQuery_length_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : (supportListQuery P J r e).1.length ≤ 12 := by
  classical
  let raw := flatMapQuery (fun t : Triangle P =>
    ([triangleVertex P t 0,triangleVertex P t 1,triangleVertex P t 2],6)) e.val.toList
  have hr : raw.1.length = 12 := by
    rw [flatMapQuery_value,flatMap_length_of_const e.val.toList _ 3 (by intro t ht; rfl)]
    simp [e.property.1]
  change (dedupQuery (fun v w : Vertex P => (decide (v=w),1)) raw.1).1.length ≤ 12
  rw [dedupQuery_value _ (by intro v w; simp)]
  exact (List.dedup_sublist raw.1).length_le.trans hr.le

theorem supportListQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : (supportListQuery P J r e).2 ≤ 378 := by
  classical
  let q := fun t : Triangle P => ([triangleVertex P t 0,triangleVertex P t 1,triangleVertex P t 2],6)
  have hr := flatMapQuery_cost_le q e.val.toList 3 6 (by intro t ht; rfl) (by intro t ht; exact le_rfl)
  have hlen : (flatMapQuery q e.val.toList).1.length = 12 := by
    rw [flatMapQuery_value,flatMap_length_of_const e.val.toList _ 3 (by intro t ht; rfl)]
    simp [e.property.1]
  have hd := dedupQuery_cost_le (fun v w : Vertex P => (decide (v=w),1))
    (by intro v w; simp) 1 (by intro v w; exact le_rfl) (flatMapQuery q e.val.toList).1
  rw [hlen] at hd
  simp only [Finset.length_toList,e.property.1] at hr
  dsimp only [supportListQuery]
  dsimp only [q] at hr hd
  omega


end QEC.Coding.BDL26RandomPerturbation
