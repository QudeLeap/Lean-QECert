import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GridPointQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedTuples
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventKeyQuery

/-! # Counted coordinate loops enumerate the actual three-dimensional integer net -/
namespace QEC.Coding.BDL26RandomPerturbation

/-- A primitive finite-label loop, including successor-label and list construction. -/
def finListQuery : (n : ℕ) → List (Fin n) × ℕ
  | 0 => ([],0)
  | n+1 => let q := finListQuery n
           let shifted := mapQuery (fun i : Fin n => (i.succ,2)) q.1
           (0::shifted.1,q.2+shifted.2+1)

theorem finListQuery_length (n : ℕ) : (finListQuery n).1.length = n := by
  induction n <;> simp_all [finListQuery,mapQuery_value]

theorem finListQuery_complete (n : ℕ) (i : Fin n) : i ∈ (finListQuery n).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finListQuery]
    · simp only [finListQuery,List.mem_cons,mapQuery_value,List.mem_map]
      exact Or.inr ⟨j,ih j,rfl⟩

theorem finListQuery_cost_le (n : ℕ) : (finListQuery n).2 ≤ 2*n^2+1 := by
  induction n with
  | zero => simp [finListQuery]
  | succ n ih =>
    have hm := mapQuery_cost_le (fun i : Fin n => (i.succ,2)) (finListQuery n).1 2 (by
      intro i hi; exact le_rfl)
    rw [finListQuery_length] at hm
    dsimp only [finListQuery]
    nlinarith

def gridCoordinateOfFin (K : ℕ) (i : Fin (2*K+1)) : GridCoordinate K :=
  ⟨(i.val : ℤ)-(K : ℤ),by
    simp only [Finset.mem_Icc]
    have hi := i.isLt
    constructor <;> omega⟩

noncomputable def gridCoordinateListQuery (K : ℕ) : List (GridCoordinate K) × ℕ :=
  let q := finListQuery (2*K+1)
  let mapped := mapQuery (fun i => (gridCoordinateOfFin K i,3)) q.1
  (mapped.1,q.2+mapped.2)

theorem gridCoordinateListQuery_length (K : ℕ) : (gridCoordinateListQuery K).1.length = 2*K+1 := by
  simp only [gridCoordinateListQuery,mapQuery_value,List.length_map,finListQuery_length]

theorem gridCoordinateListQuery_complete (K : ℕ) (g : GridCoordinate K) :
    g ∈ (gridCoordinateListQuery K).1 := by
  have hg := Finset.mem_Icc.mp g.property
  let i : Fin (2*K+1) := ⟨(g.val+(K : ℤ)).toNat,by omega⟩
  have he : gridCoordinateOfFin K i = g := by
    apply Subtype.ext
    dsimp only [gridCoordinateOfFin,i]
    omega
  simp only [gridCoordinateListQuery,mapQuery_value,List.mem_map]
  exact ⟨i,finListQuery_complete _ i,he⟩

theorem gridCoordinateListQuery_cost_le (K : ℕ) :
    (gridCoordinateListQuery K).2 ≤ 2*(2*K+1)^2+4*(2*K+1)+1 := by
  have hf := finListQuery_cost_le (2*K+1)
  have hm := mapQuery_cost_le (fun i : Fin (2*K+1) => (gridCoordinateOfFin K i,3))
    (finListQuery (2*K+1)).1 3 (by intro i hi; exact le_rfl)
  rw [finListQuery_length] at hm
  dsimp only [gridCoordinateListQuery]
  omega

noncomputable def gridRowQuery {K : ℕ} (L : List (GridCoordinate K)) (a b : GridCoordinate K) :
    List (Grid K) × ℕ := mapQuery (fun c => (![a,b,c],3)) L

noncomputable def gridPlaneQuery {K : ℕ} (L : List (GridCoordinate K)) (a : GridCoordinate K) :
    List (Grid K) × ℕ := flatMapQuery (gridRowQuery L a) L

noncomputable def gridListQuery (K : ℕ) : List (Grid K) × ℕ :=
  let coords := gridCoordinateListQuery K
  let loop := flatMapQuery (gridPlaneQuery coords.1) coords.1
  (loop.1,coords.2+loop.2)

theorem gridListQuery_complete (K : ℕ) (g : Grid K) : g ∈ (gridListQuery K).1 := by
  have h0 := gridCoordinateListQuery_complete K (g 0)
  have h1 := gridCoordinateListQuery_complete K (g 1)
  have h2 := gridCoordinateListQuery_complete K (g 2)
  have he : ![g 0,g 1,g 2] = g := by funext i; fin_cases i <;> rfl
  simp only [gridListQuery,flatMapQuery_value,gridPlaneQuery,gridRowQuery,mapQuery_value,
    List.mem_flatMap,List.mem_map]
  exact ⟨g 0,h0,g 1,h1,g 2,h2,he⟩

theorem gridRowQuery_length {K : ℕ} (L : List (GridCoordinate K)) (a b : GridCoordinate K) :
    (gridRowQuery L a b).1.length = L.length := by
  simp only [gridRowQuery,mapQuery_value,List.length_map]

theorem gridPlaneQuery_length {K : ℕ} (L : List (GridCoordinate K)) (a : GridCoordinate K) :
    (gridPlaneQuery L a).1.length = L.length^2 := by
  rw [gridPlaneQuery,flatMapQuery_value,flatMap_length_of_const L _ L.length
    (fun b hb => gridRowQuery_length L a b)]
  ring

theorem gridListQuery_length (K : ℕ) : (gridListQuery K).1.length = (2*K+1)^3 := by
  rw [gridListQuery,flatMapQuery_value,flatMap_length_of_const _ _ ((2*K+1)^2)]
  · rw [gridCoordinateListQuery_length]; ring
  · intro a ha
    rw [gridPlaneQuery_length,gridCoordinateListQuery_length]

theorem gridRowQuery_cost_le {K : ℕ} (L : List (GridCoordinate K)) (a b : GridCoordinate K) :
    (gridRowQuery L a b).2 ≤ 4*L.length := by
  simpa only [gridRowQuery,Nat.mul_comm] using
    mapQuery_cost_le (fun c : GridCoordinate K => (![a,b,c],3)) L 3 (by intro c hc; exact le_rfl)

theorem gridPlaneQuery_cost_le {K : ℕ} (L : List (GridCoordinate K)) (a : GridCoordinate K) :
    (gridPlaneQuery L a).2 ≤ 5*L.length^2+L.length := by
  have h := flatMapQuery_cost_le (gridRowQuery L a) L L.length (4*L.length)
    (fun b _ => (gridRowQuery_length L a b).le) (fun b _ => gridRowQuery_cost_le L a b)
  dsimp only [gridPlaneQuery]
  nlinarith

theorem gridListQuery_cost_le (K : ℕ) :
    (gridListQuery K).2 ≤ 6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1 := by
  have hc := gridCoordinateListQuery_cost_le K
  have h := flatMapQuery_cost_le (gridPlaneQuery (gridCoordinateListQuery K).1)
    (gridCoordinateListQuery K).1 ((2*K+1)^2) (5*(2*K+1)^2+(2*K+1))
    (by intro a ha; rw [gridPlaneQuery_length,gridCoordinateListQuery_length])
    (by intro a ha; simpa only [gridCoordinateListQuery_length] using
      gridPlaneQuery_cost_le (gridCoordinateListQuery K).1 a)
  rw [gridCoordinateListQuery_length] at h
  dsimp only [gridListQuery]
  nlinarith

end QEC.Coding.BDL26RandomPerturbation
