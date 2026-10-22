import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventEncoding

/-! # Explicit four-label input enumeration

The event universe is generated from four input-label loops, rather than an
arbitrary enumeration of the event subtype. Coincident images are distinct labels.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Four actual nested input-list loops; tuples may repeat labels at this stage. -/
def fourTuples {A : Type*} (L : List A) : List (List A) :=
  L.flatMap fun a => L.flatMap fun b => L.flatMap fun c => L.map fun d => [a,b,c,d]

theorem flatMap_length_of_const {A B : Type*} (L : List A) (f : A → List B) (C : ℕ)
    (h : ∀ a ∈ L, (f a).length = C) : (L.flatMap f).length = L.length*C := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons,List.length_append,h a (by simp),ih (fun b hb => h b (by simp [hb]))]
    simp only [List.length_cons]
    ring

theorem fourTuples_length {A : Type*} (L : List A) : (fourTuples L).length = L.length^4 := by
  have h3 (a b : A) : (L.flatMap fun c => L.map fun d => [a,b,c,d]).length = L.length*L.length :=
    flatMap_length_of_const L _ _ (fun _ _ => by simp only [List.length_map])
  have h2 (a : A) : (L.flatMap fun b => L.flatMap fun c => L.map fun d => [a,b,c,d]).length =
      L.length*(L.length*L.length) := flatMap_length_of_const L _ _ (fun b _ => h3 a b)
  rw [fourTuples,flatMap_length_of_const L _ _ (fun a _ => h2 a)]
  ring

theorem mem_fourTuples {A : Type*} (L : List A) (a b c d : A) :
    [a,b,c,d] ∈ fourTuples L ↔ a ∈ L ∧ b ∈ L ∧ c ∈ L ∧ d ∈ L := by
  simp only [fourTuples,List.mem_flatMap,List.mem_map,List.cons.injEq,
    and_true]
  aesop

/-- Every eligible event is found by these four loops over the actual input labels. -/
theorem event_in_fourTuples (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    ∃ L ∈ fourTuples (Finset.univ.toList : List (Triangle P)), L.toFinset = e.val := by
  classical
  have hlen : e.val.toList.length = 4 := by simpa using e.property.1
  obtain ⟨a,b,c,d,he⟩ := List.length_eq_four.mp hlen
  refine ⟨[a,b,c,d],?_,?_⟩
  · rw [mem_fourTuples]
    simp
  · rw [← he,Finset.toList_toFinset]

/-- All four-loop candidates have exactly four list entries, before duplicate filtering. -/
theorem fourTuples_entry_length {A : Type*} (L : List A) (t : List A)
    (h : t ∈ fourTuples L) : t.length = 4 := by
  simp only [fourTuples,List.mem_flatMap,List.mem_map] at h
  obtain ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩ := h
  rfl

end QEC.Coding.BDL26RandomPerturbation
