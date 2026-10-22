import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExecutionPrimitiveQueries

/-! # Explicit finite counter/sample rows with counted lookup and whole-row refresh

Stored rows keep each current sample together with its counter. Lookup scans this
finite input list; refresh traverses the list once. Costs depend on input length,
not on the number of preceding resampling transitions.
-/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

abbrev StateRows (P : TannerSquarePresentation) := List (Vertex P × ℕ × Space)

variable {P : TannerSquarePresentation}

noncomputable def stateRowQuery (v : Vertex P) : StateRows P → (ℕ × Space) × ℕ
  | [] => ((0,0),0)
  | row::L => if row.1=v then (row.2,2) else
      let q := stateRowQuery v L
      (q.1,q.2+2)

noncomputable def statePoints (R : StateRows P) (v : Vertex P) : Space := (stateRowQuery v R).1.2

/-- Every stored row has the exact table address and cached sample of c. -/
def StateRowsRep (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) : Prop :=
  R.map Prod.fst = vertexInputList P ∧ ∀ row ∈ R, row.2 = (c row.1,T (row.1,c row.1))

theorem stateRowQuery_cost_le (v : Vertex P) (R : StateRows P) :
    (stateRowQuery v R).2 ≤ 2*R.length := by
  induction R with
  | nil => simp [stateRowQuery]
  | cons row R ih =>
    simp only [stateRowQuery,List.length_cons]
    split_ifs <;> omega

theorem stateRowQuery_value (v : Vertex P) (R : StateRows P) (x : ℕ × Space)
    (hrows : ∀ row ∈ R, row.1=v → row.2=x) (hmem : ∃ row ∈ R, row.1=v) :
    (stateRowQuery v R).1 = x := by
  induction R with
  | nil => simp at hmem
  | cons row R ih =>
    by_cases h : row.1=v
    · simp only [stateRowQuery,h,if_true]
      exact hrows row (by simp) h
    · have hm : ∃ row ∈ R, row.1=v := by
        obtain ⟨a,ha,hav⟩ := hmem
        rcases List.mem_cons.mp ha with he|ha
        · subst a; exact False.elim (h hav)
        · exact ⟨a,ha,hav⟩
      simp only [stateRowQuery,h,if_false]
      exact ih (fun a ha hav => hrows a (by simp [ha]) hav) hm

theorem StateRowsRep_length (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    R.length = Fintype.card (Vertex P) := by
  have h := congrArg List.length hR.1
  simpa only [List.length_map,vertexInputList_length] using h

theorem StateRowsRep_points (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    statePoints R = assignment T c := by
  funext v
  have hm : ∃ row ∈ R, row.1=v := by
    have hv := vertexInputList_complete P v
    rw [← hR.1,List.mem_map] at hv
    exact hv
  have hv := stateRowQuery_value v R (c v,T (v,c v)) (by
    intro row hr hv
    subst v
    exact hR.2 row hr) hm
  exact congrArg Prod.snd hv

theorem initialRowsQuery_rep (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space)) :
    StateRowsRep P T (fun _ => 0) (initialRowsQuery P T).1 := by
  rw [initialRowsQuery_value]
  constructor
  · simp [List.map_map,Function.comp_def]
  · intro row hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    rfl

noncomputable def refreshStateRowQuery (support : List (Vertex P))
    (T : Table (X := fun _ : Vertex P => Space)) (row : Vertex P × ℕ × Space) :
    (Vertex P × ℕ × Space) × ℕ :=
  let member := memberQuery (fun v w : Vertex P => (decide (v=w),1)) row.1 support
  (if member.1 then (row.1,row.2.1+1,T (row.1,row.2.1+1)) else row,member.2+6)

theorem refreshStateRowQuery_member (support : List (Vertex P)) (v : Vertex P) :
    (memberQuery (fun v w : Vertex P => (decide (v=w),1)) v support).1 = true ↔ v ∈ support :=
  memberQuery_correct _ (by intro v w; simp) v support

theorem refreshStateRowQuery_cost_le (support : List (Vertex P))
    (T : Table (X := fun _ : Vertex P => Space)) (row : Vertex P × ℕ × Space)
    (hlen : support.length ≤ 12) : (refreshStateRowQuery support T row).2 ≤ 30 := by
  have hm := memberQuery_cost_le (fun v w : Vertex P => (decide (v=w),1)) 1
    (by intro v w; exact le_rfl) row.1 support
  dsimp only [refreshStateRowQuery]
  omega

noncomputable def refreshStateRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let support := supportListQuery P J r e
  let update := mapQuery (refreshStateRowQuery support.1 T) R
  (update.1,support.2+update.2)

theorem refreshStateRowsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (refreshStateRowsQuery P J r e T R).2 ≤ 378+32*R.length := by
  have hs := supportListQuery_cost_le P J r e
  have hm := mapQuery_cost_le (refreshStateRowQuery (supportListQuery P J r e).1 T) R 30
    (fun row _ => refreshStateRowQuery_cost_le _ T row (supportListQuery_length_le P J r e))
  dsimp only [refreshStateRowsQuery]
  omega

theorem refreshStateRowsQuery_rep (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    StateRowsRep P T (advance (eventSupport P J r) e c) (refreshStateRowsQuery P J r e T R).1 := by
  have hc (row : Vertex P × ℕ × Space) :
      (refreshStateRowQuery (supportListQuery P J r e).1 T row).1.1 = row.1 := by
    dsimp only [refreshStateRowQuery]
    split_ifs <;> rfl
  constructor
  · simp only [refreshStateRowsQuery,mapQuery_value,List.map_map,Function.comp_def]
    have he : (fun row => ((refreshStateRowQuery (supportListQuery P J r e).1 T row).1).1) = Prod.fst :=
      funext hc
    rw [he]
    exact hR.1
  · intro row hr
    simp only [refreshStateRowsQuery,mapQuery_value,List.mem_map] at hr
    obtain ⟨old,hold,rfl⟩ := hr
    have hval := hR.2 old hold
    by_cases hv : old.1 ∈ eventSupport P J r e
    · have hm := (refreshStateRowQuery_member (supportListQuery P J r e).1 old.1).mpr
        ((supportListQuery_mem P J r e old.1).mpr hv)
      have hnew : (refreshStateRowQuery (supportListQuery P J r e).1 T old).1 =
          (old.1,c old.1+1,T (old.1,c old.1+1)) := by
        simp only [refreshStateRowQuery,hm,if_true]
        rw [hval]
      rw [hnew,advance_of_mem _ _ _ hv]
    · have hm : (memberQuery (fun v w : Vertex P => (decide (v=w),1)) old.1 (supportListQuery P J r e).1).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hv ((supportListQuery_mem P J r e old.1).mp
          ((refreshStateRowQuery_member _ old.1).mp h)))
      have hnew : (refreshStateRowQuery (supportListQuery P J r e).1 T old).1 = old := by
        simp [refreshStateRowQuery,hm]
      rw [hnew,hval,advance_of_notMem _ _ _ hv]

noncomputable def outputStateRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (R : StateRows P) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun row => let q := pointSnapshotQuery lambda (J row.1) row.2.2
                       ((row.1,q.1),q.2+3)) R

theorem outputStateRowsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (R : StateRows P) : (outputStateRowsQuery P J lambda R).2 ≤ 49*R.length := by
  have h := mapQuery_cost_le (fun row : Vertex P × ℕ × Space =>
    let q := pointSnapshotQuery lambda (J row.1) row.2.2
    ((row.1,q.1),q.2+3)) R 48 (by
      intro row hr
      have hq := pointSnapshotQuery_cost_le lambda (J row.1) row.2.2
      dsimp only
      omega)
  simpa only [outputStateRowsQuery,Nat.mul_comm] using h

/-- The actual emitted row list equals the perturbed map of the represented execution state. -/
theorem outputStateRowsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (hR : StateRowsRep P T c R) :
    (outputStateRowsQuery P J lambda R).1 = (vertexInputList P).map
      (fun v => (v,lambda • ((1/2 : ℝ) • J v)+assignment T c v)) := by
  rw [outputStateRowsQuery,mapQuery_value]
  have he : R.map (fun row => (row.1,(pointSnapshotQuery lambda (J row.1) row.2.2).1)) =
      R.map (fun row => (row.1,lambda • ((1/2 : ℝ) • J row.1)+assignment T c row.1)) := by
    apply List.map_congr_left
    intro row hr
    have hv := congrArg Prod.snd (hR.2 row hr)
    simp only [pointSnapshotQuery_value,assignment,tableRead,hv]
  rw [he]
  change R.map ((fun v => (v,lambda • ((1/2 : ℝ) • J v)+assignment T c v)) ∘ Prod.fst) = _
  rw [← List.map_map,hR.1]

end QEC.Coding.BDL26RandomPerturbation
