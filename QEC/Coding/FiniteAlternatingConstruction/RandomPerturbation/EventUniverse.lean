import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EligibleListQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedTuples
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedScan

/-! # The actual counted input loops construct the execution's sorted event universe -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Input rank labels enumerate all eligible four-triangle events. -/
theorem event_in_triangleInputTuples (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    ∃ L ∈ fourTuples (triangleInputList P), L.toFinset = e.val := by
  classical
  have hlen : e.val.toList.length = 4 := by simpa using e.property.1
  obtain ⟨a,b,c,d,he⟩ := List.length_eq_four.mp hlen
  have hm (t : Triangle P) : t ∈ triangleInputList P := by
    rw [← List.mem_toFinset,triangleInputList_toFinset]
    exact Finset.mem_univ t
  refine ⟨[a,b,c,d],(mem_fourTuples _ a b c d).mpr ⟨hm a,hm b,hm c,hm d⟩,?_⟩
  rw [← he,Finset.toList_toFinset]

noncomputable def rawEventUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P J r) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (candidateEventQuery P J hr) tuples.1
  (events.1,tuples.2+events.2)

theorem rawEventUniverse_complete (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (e : Event P J r) : e ∈ (rawEventUniverseQuery P J hr).1 := by
  classical
  obtain ⟨L,hL,he⟩ := event_in_triangleInputTuples P J r e
  simp only [rawEventUniverseQuery,filterMapQuery_value,fourTuplesQuery_value,List.mem_filterMap]
  exact ⟨L,hL,(candidateEventQuery_some_iff P J hr L e).mpr he⟩

theorem rawEventUniverse_length_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : (rawEventUniverseQuery P J hr).1.length ≤ Fintype.card (Triangle P)^4 := by
  have h := filterMapQuery_length_le (candidateEventQuery P J hr) (fourTuplesQuery (triangleInputList P)).1
  simpa only [rawEventUniverseQuery,fourTuplesQuery_value,fourTuples_length,triangleInputList_length] using h

noncomputable def eventEqQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : Bool × ℕ :=
  let forward := eventCompareQuery P J r e f
  let backward := eventCompareQuery P J r f e
  (forward.1 && backward.1,forward.2+backward.2+1)

theorem eventEqQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : (eventEqQuery P J r e f).1 = true ↔ e = f := by
  simp only [eventEqQuery,Bool.and_eq_true,eventCompareQuery_correct]
  constructor
  · intro h
    exact eventScanKey_injective P J r (le_antisymm h.1 h.2)
  · rintro rfl
    exact ⟨le_rfl,le_rfl⟩

theorem eventEqQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (eventEqQuery P J r e f).2 ≤ 16*(Fintype.card (Triangle P)+1)+219 := by
  have hf := eventCompareQuery_cost_le P J r e f
  have hb := eventCompareQuery_cost_le P J r f e
  dsimp only [eventEqQuery]
  omega

theorem eventCompareQuery_priority_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : (eventCompareQuery P J r e f).1 = true ↔ eventPriorityLE P J r e f :=
  eventCompareQuery_correct P J r e f

noncomputable def eventUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P J r) × ℕ :=
  let raw := rawEventUniverseQuery P J hr
  let unique := dedupQuery (eventEqQuery P J r) raw.1
  let sorted := sortQuery (eventCompareQuery P J r) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)

/-- The counted finite construction supplies exactly the order used in actual resampling. -/
theorem eventUniverseQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (eventUniverseQuery P J hr).1 = (Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r) := by
  classical
  let raw := (rawEventUniverseQuery P J hr).1
  have hu : raw.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    exact List.mem_toFinset.mpr (rawEventUniverse_complete P J hr e)
  have hn := List.nodup_dedup raw
  have he : raw.dedup.toFinset = (Finset.univ : Finset (Event P J r)) := by
    calc
      raw.dedup.toFinset = raw.toFinset := by
        ext e
        simp only [List.mem_toFinset,List.mem_dedup]
      _ = Finset.univ := hu
  have hperm : List.Perm ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) raw.dedup := by
    rw [← he]
    exact (Finset.sort_perm_toList _ _).trans (List.toFinset_toList hn)
  have hsort : (Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r) = raw.dedup.insertionSort (eventPriorityLE P J r) :=
    (hperm.trans (List.perm_insertionSort (eventPriorityLE P J r) raw.dedup).symm).eq_of_pairwise'
      (Finset.pairwise_sort _ _) (List.pairwise_insertionSort _ _)
  change (sortQuery (eventCompareQuery P J r) (dedupQuery (eventEqQuery P J r) raw).1).1 = _
  rw [sortQuery_value _ (eventPriorityLE P J r) (eventCompareQuery_priority_correct P J r),
    dedupQuery_value _ (eventEqQuery_correct P J r)]
  exact hsort.symm

end QEC.Coding.BDL26RandomPerturbation
