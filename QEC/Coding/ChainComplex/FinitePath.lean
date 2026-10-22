import QEC.Coding.ChainComplex.Cohomology

/-!
# Finite path incidence

The auxiliary cells in HHO20 weight reduction are ordinary path edges between
consecutive ordered incidences.  This module proves their boundary/coboundary
duality without any dependent Tanner-graph indices.
-/

namespace QEC.Coding.FinitePath

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- Left endpoint of path edge `j` in a path with `n + 1` vertices. -/
def left {n : Nat} (j : Fin n) : Fin (n + 1) := ⟨j.1, by omega⟩

/-- Right endpoint of path edge `j`. -/
def right {n : Nat} (j : Fin n) : Fin (n + 1) := ⟨j.1 + 1, by omega⟩

/-- Path edge immediately before vertex `i`, if present. -/
def previous {n : Nat} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : 0 < i.1 then some ⟨i.1 - 1, by omega⟩ else none

/-- Path edge immediately after vertex `i`, if present. -/
def next {n : Nat} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.1 < n then some ⟨i.1, by omega⟩ else none

/-- A word supported at an optional coordinate. -/
def optionalSingle {Index : Type*} [DecidableEq Index]
    (o : Option Index) : Word F Index :=
  match o with
  | none => 0
  | some i => Pi.single i 1

/-- Coboundary of a path vertex: its preceding and following path edges. -/
def vertexCoboundary {n : Nat} (i : Fin (n + 1)) : Word F (Fin n) :=
  optionalSingle (F := F) (previous i) + optionalSingle (F := F) (next i)

/-- Boundary of a path edge: its two endpoints. -/
def edgeBoundary {n : Nat} (j : Fin n) : Word F (Fin (n + 1)) :=
  Pi.single (left j) 1 + Pi.single (right j) 1

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem optionalSingle_previous_apply {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    optionalSingle (F := F) (previous i) j = if right j = i then 1 else 0 := by
  classical
  by_cases hi : 0 < i.1
  · by_cases hRight : right j = i
    · subst i
      simp [previous, optionalSingle, right]
    · have hne : (⟨i.1 - 1, by omega⟩ : Fin n) ≠ j := by
        intro h
        apply hRight
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simp [right]
        omega
      simp [previous, hi, optionalSingle, hRight, hne]
  · have hRight : right j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [right] at hv
      omega
    simp [previous, hi, optionalSingle, hRight]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem optionalSingle_next_apply {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    optionalSingle (F := F) (next i) j = if left j = i then 1 else 0 := by
  classical
  by_cases hi : i.1 < n
  · by_cases hLeft : left j = i
    · subst i
      simp [next, optionalSingle, left]
    · have hne : (⟨i.1, hi⟩ : Fin n) ≠ j := by
        intro h
        apply hLeft
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simpa [left] using hv.symm
      simp [next, hi, optionalSingle, hLeft, hne]
  · have hLeft : left j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [left] at hv
      omega
    simp [next, hi, optionalSingle, hLeft]

omit [Fintype F] [DecidableEq F] in
/-- Vertex-edge incidence is symmetric between the path boundary and
coboundary descriptions. -/
theorem vertexCoboundary_apply_eq_edgeBoundary_apply
    {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    vertexCoboundary (F := F) i j = edgeBoundary (F := F) j i := by
  classical
  unfold vertexCoboundary edgeBoundary
  simp only [Pi.add_apply, optionalSingle_previous_apply,
    optionalSingle_next_apply, Pi.single_apply]
  by_cases hLeft : left j = i
  · have hLeft' : i = left j := hLeft.symm
    by_cases hRight : right j = i
    · have hRight' : i = right j := hRight.symm
      rw [if_pos hRight, if_pos hLeft, if_pos hLeft', if_pos hRight']
    · have hRight' : i ≠ right j := fun h => hRight h.symm
      rw [if_neg hRight, if_pos hLeft, if_pos hLeft', if_neg hRight']
      simp only [zero_add, add_zero]
  · have hLeft' : i ≠ left j := fun h => hLeft h.symm
    by_cases hRight : right j = i
    · have hRight' : i = right j := hRight.symm
      rw [if_pos hRight, if_neg hLeft, if_neg hLeft', if_pos hRight']
      simp only [zero_add, add_zero]
    · have hRight' : i ≠ right j := fun h => hRight h.symm
      rw [if_neg hRight, if_neg hLeft, if_neg hLeft', if_neg hRight']

/-- Linear boundary from path vertices to path edges. -/
def boundary {n : Nat} : Word F (Fin (n + 1)) →ₗ[F] Word F (Fin n) where
  toFun x j := ∑ i : Fin (n + 1), x i * vertexCoboundary (F := F) i j
  map_add' x y := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' coefficient x := by
    ext j
    simp [Finset.mul_sum, mul_assoc]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem boundary_single {n : Nat} (i : Fin (n + 1)) :
    boundary (F := F) (Pi.single i 1) = vertexCoboundary (F := F) i := by
  classical
  ext j
  unfold boundary
  dsimp
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
  · simp

omit [DecidableEq F] in
/-- The transpose row of the path boundary is exactly the endpoint boundary. -/
theorem transpose_boundary_single {n : Nat} (j : Fin n) :
    wordLinearMapTranspose (boundary (F := F)) (Pi.single j 1) =
      edgeBoundary (F := F) j := by
  classical
  ext i
  unfold wordLinearMapTranspose boundary
  dsimp
  rw [Fintype.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_mul]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_mul]
      exact vertexCoboundary_apply_eq_edgeBoundary_apply (F := F) i j
    · intro i' _ hne
      simp [hne]
    · simp
  · intro j' hne
    rw [Pi.single_eq_of_ne hne, zero_mul]

omit [Fintype F] in
theorem HammingWeight_single_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index] (i : Index) :
    HammingWeight (Pi.single i (1 : F) : Word F Index) ≤ 1 := by
  classical
  rw [HammingWeight_eq_card_hammingSupport]
  apply (Finset.card_le_card (s := hammingSupport
    (Pi.single i (1 : F) : Word F Index)) (t := {i}))
  intro j hj
  simp only [Finset.mem_singleton]
  by_contra hji
  have hzero : (Pi.single i (1 : F) : Word F Index) j = 0 := by
    rw [Pi.single_eq_of_ne hji]
  simp [hammingSupport, hzero] at hj

omit [Fintype F] in
theorem HammingWeight_optionalSingle_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (o : Option Index) : HammingWeight (optionalSingle (F := F) o) ≤ 1 := by
  cases o with
  | none => simp [optionalSingle]
  | some i => exact HammingWeight_single_le_one (F := F) i

omit [Fintype F] in
/-- Every path vertex is incident to at most two path edges. -/
theorem HammingWeight_vertexCoboundary_le_two {n : Nat} (i : Fin (n + 1)) :
    HammingWeight (vertexCoboundary (F := F) i) ≤ 2 := by
  unfold vertexCoboundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_optionalSingle_le_one (F := F) _)
      (HammingWeight_optionalSingle_le_one (F := F) _))

omit [Fintype F] in
/-- Every path edge has exactly two candidate endpoints, hence weight at most
two over any field. -/
theorem HammingWeight_edgeBoundary_le_two {n : Nat} (j : Fin n) :
    HammingWeight (edgeBoundary (F := F) j) ≤ 2 := by
  unfold edgeBoundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_single_le_one (F := F) _)
      (HammingWeight_single_le_one (F := F) _))

end QEC.Coding.FinitePath
