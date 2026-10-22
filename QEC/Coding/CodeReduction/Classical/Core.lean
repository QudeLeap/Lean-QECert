import QEC.Coding.ChainComplex.HomotopyDistance

/-!
# HHO20 classical Tanner-graph weight reduction

This file implements the primary and auxiliary cells in Appendix A of HHO20.
Every original Tanner incidence becomes both a primary bit and a primary
check.  Consecutive incidences at an original bit are joined by auxiliary
checks, while consecutive incidences at an original check are joined by
auxiliary bits.
-/

namespace QEC.Coding.ClassicalWeightReduction

open scoped BigOperators

universe u v w

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]

/-- One nonzero Tanner-matrix entry. -/
abbrev Incidence := { edge : Check × Bit // R edge.1 edge.2 }

/-- Checks incident to one original bit. -/
abbrev BitNeighbor (b : Bit) := { c : Check // R c b }

/-- Bits incident to one original check. -/
abbrev CheckNeighbor (c : Check) := { b : Bit // R c b }

/-- A fixed ordering of the checks incident to an original bit. -/
noncomputable def bitNeighborOrder (b : Bit) :
    Fin (Fintype.card (BitNeighbor R b)) ≃ BitNeighbor R b :=
  (Fintype.equivFin (BitNeighbor R b)).symm

/-- A fixed ordering of the bits incident to an original check. -/
noncomputable def checkNeighborOrder (c : Check) :
    Fin (Fintype.card (CheckNeighbor R c)) ≃ CheckNeighbor R c :=
  (Fintype.equivFin (CheckNeighbor R c)).symm

/-- The incidence occupying position `i` around bit `b`. -/
noncomputable def bitIncidenceAt (b : Bit)
    (i : Fin (Fintype.card (BitNeighbor R b))) : Incidence R :=
  ⟨((bitNeighborOrder R b i).1, b), (bitNeighborOrder R b i).2⟩

/-- The incidence occupying position `i` around check `c`. -/
noncomputable def checkIncidenceAt (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) : Incidence R :=
  ⟨(c, (checkNeighborOrder R c i).1), (checkNeighborOrder R c i).2⟩

/-- The position of an incidence in the ordering around its bit. -/
noncomputable def bitPosition (e : Incidence R) :
    Fin (Fintype.card (BitNeighbor R e.1.2)) :=
  (bitNeighborOrder R e.1.2).symm ⟨e.1.1, e.2⟩

/-- The position of an incidence in the ordering around its check. -/
noncomputable def checkPosition (e : Incidence R) :
    Fin (Fintype.card (CheckNeighbor R e.1.1)) :=
  (checkNeighborOrder R e.1.1).symm ⟨e.1.2, e.2⟩

omit [DecidableEq Check] [Fintype Bit] [DecidableEq Bit] in
@[simp]
theorem bitIncidenceAt_bitPosition (e : Incidence R) :
    bitIncidenceAt R e.1.2 (bitPosition R e) = e := by
  apply Subtype.ext
  simp [bitIncidenceAt, bitPosition]

omit [Fintype Check] [DecidableEq Check] [DecidableEq Bit] in
@[simp]
theorem checkIncidenceAt_checkPosition (e : Incidence R) :
    checkIncidenceAt R e.1.1 (checkPosition R e) = e := by
  apply Subtype.ext
  simp [checkIncidenceAt, checkPosition]

omit [DecidableEq Check] [Fintype Bit] [DecidableEq Bit] in
@[simp]
theorem bitPosition_bitIncidenceAt (b : Bit)
    (i : Fin (Fintype.card (BitNeighbor R b))) :
    bitPosition R (bitIncidenceAt R b i) = i := by
  exact (bitNeighborOrder R b).symm_apply_apply i

omit [Fintype Check] [DecidableEq Check] [DecidableEq Bit] in
@[simp]
theorem checkPosition_checkIncidenceAt (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    checkPosition R (checkIncidenceAt R c i) = i := by
  exact (checkNeighborOrder R c).symm_apply_apply i

/-- Left endpoint of the `j`th edge in a path with `n` vertices. -/
def pathLeft {n : Nat} (j : Fin (n - 1)) : Fin n :=
  ⟨j.1, by omega⟩

/-- Right endpoint of the `j`th edge in a path with `n` vertices. -/
def pathRight {n : Nat} (j : Fin (n - 1)) : Fin n :=
  ⟨j.1 + 1, by omega⟩

/-- A word supported at the optional coordinate `o`. -/
def optionalSingle {Index : Type*} [DecidableEq Index]
    (o : Option Index) : Word F Index :=
  match o with
  | none => 0
  | some i => Pi.single i 1

/-- Path edge immediately before a path vertex, when it exists. -/
def pathPrevious {n : Nat} (i : Fin n) : Option (Fin (n - 1)) :=
  if h : 0 < i.1 then some ⟨i.1 - 1, by omega⟩ else none

/-- Path edge immediately after a path vertex, when it exists. -/
def pathNext {n : Nat} (i : Fin n) : Option (Fin (n - 1)) :=
  if h : i.1 + 1 < n then some ⟨i.1, by omega⟩ else none

omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_pathPrevious_apply {n : Nat} (i : Fin n)
    (j : Fin (n - 1)) :
    optionalSingle (F := F) (pathPrevious i) j =
      if pathRight j = i then 1 else 0 := by
  classical
  by_cases hi : 0 < i.1
  · by_cases hRight : pathRight j = i
    · subst i
      simp [pathPrevious, optionalSingle, pathRight]
    · have hne : (⟨i.1 - 1, by omega⟩ : Fin (n - 1)) ≠ j := by
        intro h
        apply hRight
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simp [pathRight]
        omega
      simp [pathPrevious, hi, optionalSingle, hRight, hne]
  · have hRight : pathRight j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [pathRight] at hv
      omega
    simp [pathPrevious, hi, optionalSingle, hRight]

omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_pathNext_apply {n : Nat} (i : Fin n)
    (j : Fin (n - 1)) :
    optionalSingle (F := F) (pathNext i) j =
      if pathLeft j = i then 1 else 0 := by
  classical
  by_cases hi : i.1 + 1 < n
  · by_cases hLeft : pathLeft j = i
    · subst i
      have hj : j.1 + 1 < n := by omega
      simp [pathNext, optionalSingle, pathLeft, hj]
    · have hne : (⟨i.1, by omega⟩ : Fin (n - 1)) ≠ j := by
        intro h
        apply hLeft
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simpa [pathLeft] using hv.symm
      simp [pathNext, hi, optionalSingle, hLeft, hne]
  · have hLeft : pathLeft j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [pathLeft] at hv
      omega
    simp [pathNext, hi, optionalSingle, hLeft]

omit [Fintype F] [DecidableEq F] [Fintype Check] in
/-- Incidence of a vertex with a truncated path edge is symmetric between
the predecessor/successor and endpoint descriptions. -/
theorem pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply {n : Nat}
    (i : Fin n) (j : Fin (n - 1)) :
    (optionalSingle (F := F) (pathPrevious i) +
        optionalSingle (F := F) (pathNext i)) j =
      (Pi.single (pathLeft j) 1 + Pi.single (pathRight j) 1 : Word F (Fin n)) i := by
  classical
  simp only [Pi.add_apply, optionalSingle_pathPrevious_apply,
    optionalSingle_pathNext_apply, Pi.single_apply]
  by_cases hLeft : pathLeft j = i
  · have hLeft' : i = pathLeft j := hLeft.symm
    by_cases hRight : pathRight j = i
    · have hRight' : i = pathRight j := hRight.symm
      rw [if_pos hRight, if_pos hLeft, if_pos hLeft', if_pos hRight']
    · have hRight' : i ≠ pathRight j := fun h => hRight h.symm
      rw [if_neg hRight, if_pos hLeft, if_pos hLeft', if_neg hRight']
      simp only [zero_add, add_zero]
  · have hLeft' : i ≠ pathLeft j := fun h => hLeft h.symm
    by_cases hRight : pathRight j = i
    · have hRight' : i = pathRight j := hRight.symm
      rw [if_pos hRight, if_neg hLeft, if_neg hLeft', if_pos hRight']
      simp only [zero_add, add_zero]
    · have hRight' : i ≠ pathRight j := fun h => hRight h.symm
      rw [if_neg hRight, if_neg hLeft, if_neg hLeft', if_neg hRight']

omit [Fintype F] [DecidableEq F] [Fintype Check] in
@[simp]
theorem optionalSingle_map_inr_apply_inl
    {Left Right Source : Type*} [DecidableEq (Left ⊕ Right)]
    (o : Option Source) (f : Source → Right) (x : Left) :
    optionalSingle (F := F) (o.map (fun y => Sum.inr (f y))) (Sum.inl x) = 0 := by
  cases o <;> simp [optionalSingle]

/-- One auxiliary check for each consecutive pair of incidences at a bit. -/
abbrev AuxiliaryCheck :=
  Σ b : Bit, Fin (Fintype.card (BitNeighbor R b) - 1)

/-- One auxiliary bit for each consecutive pair of incidences at a check. -/
abbrev AuxiliaryBit :=
  Σ c : Check, Fin (Fintype.card (CheckNeighbor R c) - 1)

/-- Bits of the HHO20 weight-reduced classical code. -/
abbrev WeightReducedBit := Incidence R ⊕ AuxiliaryBit R

/-- Checks of the HHO20 weight-reduced classical code. -/
abbrev WeightReducedCheck := Incidence R ⊕ AuxiliaryCheck R

/-- Embed a path edge at bit `b` as an auxiliary-check coordinate. -/
def auxiliaryCheckIndex (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    WeightReducedCheck R :=
  Sum.inr ⟨b, j⟩

/-- Embed a path edge at check `c` as an auxiliary-bit coordinate. -/
def auxiliaryBitIndex (c : Check)
    (j : Fin (Fintype.card (CheckNeighbor R c) - 1)) :
    WeightReducedBit R :=
  Sum.inr ⟨c, j⟩

omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_map_auxiliaryCheckIndex_apply_same
    (b : Bit) (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))
        (Sum.inr ⟨b, j⟩) = optionalSingle (F := F) o j := by
  cases o with
  | none => rfl
  | some k =>
      by_cases hk : k = j
      · subst j
        simp [optionalSingle, auxiliaryCheckIndex]
      · have hs : (Sum.inr ⟨b, k⟩ : WeightReducedCheck R) ≠ Sum.inr ⟨b, j⟩ := by
          intro h
          apply hk
          exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h) |>.2)
        simp [optionalSingle, auxiliaryCheckIndex, hk, hs]

omit [Fintype F] [DecidableEq F] [Fintype Bit] in
theorem optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
    {b b' : Bit} (hb : b ≠ b')
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (j : Fin (Fintype.card (BitNeighbor R b') - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))
        (Sum.inr ⟨b', j⟩) = 0 := by
  cases o <;> simp [optionalSingle, auxiliaryCheckIndex, hb]

omit [Fintype F] [DecidableEq F] [Fintype Check] in
@[simp]
theorem optionalSingle_map_auxiliaryBitIndex_apply_same
    (c : Check) (o : Option (Fin (Fintype.card (CheckNeighbor R c) - 1)))
    (j : Fin (Fintype.card (CheckNeighbor R c) - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryBitIndex R c))
        (Sum.inr ⟨c, j⟩) = optionalSingle (F := F) o j := by
  cases o with
  | none => rfl
  | some k =>
      by_cases hk : k = j
      · subst j
        simp [optionalSingle, auxiliaryBitIndex]
      · have hs : (Sum.inr ⟨c, k⟩ : WeightReducedBit R) ≠ Sum.inr ⟨c, j⟩ := by
          intro h
          apply hk
          exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h) |>.2)
        simp [optionalSingle, auxiliaryBitIndex, hk, hs]

omit [Fintype F] [DecidableEq F] [Fintype Check] in
theorem optionalSingle_map_auxiliaryBitIndex_apply_of_ne
    {c c' : Check} (hc : c ≠ c')
    (o : Option (Fin (Fintype.card (CheckNeighbor R c) - 1)))
    (j : Fin (Fintype.card (CheckNeighbor R c') - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryBitIndex R c))
        (Sum.inr ⟨c', j⟩) = 0 := by
  cases o <;> simp [optionalSingle, auxiliaryBitIndex, hc]

omit [Fintype F] [DecidableEq F] in
theorem single_bitIncidenceAt_apply (e : Incidence R)
    (k : Fin (Fintype.card (BitNeighbor R e.1.2))) :
    (Pi.single (Sum.inl (bitIncidenceAt R e.1.2 k)) 1 :
        Word F (WeightReducedBit R)) (Sum.inl e) =
      (Pi.single k 1 : Word F
        (Fin (Fintype.card (BitNeighbor R e.1.2)))) (bitPosition R e) := by
  classical
  by_cases hk : k = bitPosition R e
  · subst k
    rw [bitIncidenceAt_bitPosition R e]
    simp
  · have he : bitIncidenceAt R e.1.2 k ≠ e := by
      intro h
      apply hk
      have hn : bitNeighborOrder R e.1.2 k = ⟨e.1.1, e.2⟩ := by
        apply Subtype.ext
        exact congrArg (fun x : Incidence R => x.1.1) h
      have hp := congrArg (bitNeighborOrder R e.1.2).symm hn
      simpa [bitPosition] using hp
    simp [hk, he]

omit [Fintype F] [DecidableEq F] in
theorem single_bitIncidenceAt_apply_of_ne {b : Bit} (e : Incidence R)
    (hb : e.1.2 ≠ b) (k : Fin (Fintype.card (BitNeighbor R b))) :
    (Pi.single (Sum.inl (bitIncidenceAt R b k)) 1 :
        Word F (WeightReducedBit R)) (Sum.inl e) = 0 := by
  classical
  have he : bitIncidenceAt R b k ≠ e := by
    intro h
    apply hb
    have hv := congrArg (fun x : Incidence R => x.1.2) h
    simpa [bitIncidenceAt] using hv.symm
  simp [he]

omit [Fintype F] [DecidableEq F] in
theorem single_checkIncidenceAt_apply (e : Incidence R)
    (k : Fin (Fintype.card (CheckNeighbor R e.1.1))) :
    (Pi.single (Sum.inl (checkIncidenceAt R e.1.1 k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) =
      (Pi.single k 1 : Word F
        (Fin (Fintype.card (CheckNeighbor R e.1.1)))) (checkPosition R e) := by
  classical
  by_cases hk : k = checkPosition R e
  · subst k
    rw [checkIncidenceAt_checkPosition R e]
    simp
  · have he : checkIncidenceAt R e.1.1 k ≠ e := by
      intro h
      apply hk
      have hn : checkNeighborOrder R e.1.1 k = ⟨e.1.2, e.2⟩ := by
        apply Subtype.ext
        exact congrArg (fun x : Incidence R => x.1.2) h
      have hp := congrArg (checkNeighborOrder R e.1.1).symm hn
      simpa [checkPosition] using hp
    simp [hk, he]

omit [Fintype F] [DecidableEq F] in
theorem single_checkIncidenceAt_apply_of_ne {c : Check} (e : Incidence R)
    (hc : e.1.1 ≠ c) (k : Fin (Fintype.card (CheckNeighbor R c))) :
    (Pi.single (Sum.inl (checkIncidenceAt R c k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) = 0 := by
  classical
  have he : checkIncidenceAt R c k ≠ e := by
    intro h
    apply hc
    have hv := congrArg (fun x : Incidence R => x.1.1) h
    simpa [checkIncidenceAt] using hv.symm
  simp [he]

/-- The boundary of one primary bit. -/
noncomputable def primaryBitBoundary (e : Incidence R) :
    Word F (WeightReducedCheck R) :=
  Pi.single (Sum.inl e) 1 +
    optionalSingle (F := F)
      ((pathPrevious (bitPosition R e)).map (auxiliaryCheckIndex R e.1.2)) +
    optionalSingle (F := F)
      ((pathNext (bitPosition R e)).map (auxiliaryCheckIndex R e.1.2))

/-- The boundary of one auxiliary bit: the two adjacent primary checks. -/
noncomputable def auxiliaryBitBoundary (a : AuxiliaryBit R) :
    Word F (WeightReducedCheck R) :=
  Pi.single
      (Sum.inl (checkIncidenceAt R a.1 (pathLeft a.2))) 1 +
    Pi.single
      (Sum.inl (checkIncidenceAt R a.1 (pathRight a.2))) 1

/-- The coboundary of one primary check.  It consists of its matching primary
bit and the at most two adjacent auxiliary bits along the check path. -/
noncomputable def primaryCheckCoboundary (e : Incidence R) :
    Word F (WeightReducedBit R) :=
  Pi.single (Sum.inl e) 1 +
    optionalSingle (F := F)
      ((pathPrevious (checkPosition R e)).map (auxiliaryBitIndex R e.1.1)) +
    optionalSingle (F := F)
      ((pathNext (checkPosition R e)).map (auxiliaryBitIndex R e.1.1))

/-- The coboundary of one auxiliary check: the two adjacent primary bits. -/
noncomputable def auxiliaryCheckCoboundary (a : AuxiliaryCheck R) :
    Word F (WeightReducedBit R) :=
  Pi.single
      (Sum.inl (bitIncidenceAt R a.1 (pathLeft a.2))) 1 +
    Pi.single
      (Sum.inl (bitIncidenceAt R a.1 (pathRight a.2))) 1

/-- Intended coboundary image of a weight-reduced basis check. -/
noncomputable def basisCoboundary : WeightReducedCheck R →
    Word F (WeightReducedBit R)
  | Sum.inl e => primaryCheckCoboundary (F := F) R e
  | Sum.inr a => auxiliaryCheckCoboundary (F := F) R a

/-- Boundary image of a weight-reduced basis bit. -/
noncomputable def basisBoundary : WeightReducedBit R →
    Word F (WeightReducedCheck R)
  | Sum.inl e => primaryBitBoundary (F := F) R e
  | Sum.inr a => auxiliaryBitBoundary (F := F) R a

/-- The linear map determined by images of finite-coordinate basis words. -/
noncomputable def linearMapOfBasisImages
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) :
    Word F Source →ₗ[F] Word F Target where
  toFun x := ∑ i : Source, x i • image i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' coefficient x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply]
    simp only [smul_eq_mul]

/-- The HHO20 classical weight-reduced boundary operator. -/
noncomputable def boundary :
    Word F (WeightReducedBit R) →ₗ[F]
      Word F (WeightReducedCheck R) :=
  linearMapOfBasisImages (F := F) (basisBoundary (F := F) R)

/-- Boundary column of an original Tanner bit. -/
noncomputable def originalBasisBoundary (b : Bit) : Word F Check :=
  fun c => if R c b then 1 else 0

/-- Boundary operator of the original Tanner code. -/
noncomputable def originalBoundary : Word F Bit →ₗ[F] Word F Check :=
  linearMapOfBasisImages (F := F) (originalBasisBoundary (F := F) R)

section SameUniverseComplex

universe x

variable {F₀ Check₀ Bit₀ : Type x}
variable [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable [Fintype Check₀] [DecidableEq Check₀]
variable [Fintype Bit₀] [DecidableEq Bit₀]
variable (R₀ : Check₀ → Bit₀ → Prop) [DecidableRel R₀]

/-- The original Tanner code as a three-term complex with zero degree two.
The code coordinates and coefficient field are placed in one universe because
`ChainComplexData` uses a common universe for all three chain groups. -/
noncomputable def originalComplex :
    ChainComplexData F₀ (Word F₀ Check₀) (Word F₀ Bit₀)
      (Word F₀ (Fin 0)) where
  boundary1 := originalBoundary (F := F₀) R₀
  boundary2 := 0
  boundary_squared := by simp

/-- The HHO20 weight-reduced Tanner code as a three-term complex with zero
degree two. -/
noncomputable def weightReducedComplex :
    ChainComplexData F₀ (Word F₀ (WeightReducedCheck R₀))
      (Word F₀ (WeightReducedBit R₀)) (Word F₀ (Fin 0)) where
  boundary1 := boundary (F := F₀) R₀
  boundary2 := 0
  boundary_squared := by simp

end SameUniverseComplex

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem linearMapOfBasisImages_single
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) (i : Source) :
    linearMapOfBasisImages (F := F) image (Pi.single i 1) = image i := by
  classical
  unfold linearMapOfBasisImages
  change (∑ j : Source, (Pi.single i (1 : F) : Word F Source) j • image j) =
    image i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp

omit [DecidableEq F] in
/-- Transposing a basis-image linear map exposes one matrix row. -/
theorem wordLinearMapTranspose_linearMapOfBasisImages_single
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) (q : Target) :
    wordLinearMapTranspose (linearMapOfBasisImages (F := F) image)
        (Pi.single q 1) = fun i => image i q := by
  classical
  ext i
  unfold wordLinearMapTranspose linearMapOfBasisImages
  dsimp
  rw [Fintype.sum_eq_single q]
  · simp only [Pi.single_eq_same, one_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      simp [hne]
    · simp
  · intro q' hne
    simp [hne]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem originalBoundary_single (b : Bit) :
    originalBoundary (F := F) R (Pi.single b 1) =
      originalBasisBoundary (F := F) R b := by
  exact linearMapOfBasisImages_single (F := F) _ _

omit [DecidableEq F] in
/-- A row of the transposed original Tanner boundary is its incidence word. -/
theorem transpose_originalBoundary_single (c : Check) :
    wordLinearMapTranspose (originalBoundary (F := F) R) (Pi.single c 1) =
      fun b => if R c b then 1 else 0 := by
  unfold originalBoundary
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  rfl

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem boundary_single (i : WeightReducedBit R) :
    boundary (F := F) R (Pi.single i 1) = basisBoundary (F := F) R i := by
  exact linearMapOfBasisImages_single (F := F) _ _

omit [Fintype F] [DecidableEq F] in
/-- The explicitly described boundary and coboundary basis images are entries
of the same Tanner matrix. -/
theorem basisBoundary_apply_eq_basisCoboundary_apply
    (i : WeightReducedBit R) (q : WeightReducedCheck R) :
    basisBoundary (F := F) R i q = basisCoboundary (F := F) R q i := by
  classical
  cases i with
  | inl e =>
      cases q with
      | inl e' =>
          unfold basisBoundary basisCoboundary primaryBitBoundary
            primaryCheckCoboundary auxiliaryCheckIndex auxiliaryBitIndex
          simp only [Pi.add_apply, optionalSingle_map_inr_apply_inl,
            add_zero, Pi.single_apply]
          by_cases h : e = e'
          · subst e'
            rw [if_pos rfl, if_pos rfl]
          · have h' : e' ≠ e := fun heq => h heq.symm
            have hsCheck : (Sum.inl e' : WeightReducedCheck R) ≠ Sum.inl e := by
              exact fun heq => h' (Sum.inl.inj heq)
            have hsBit : (Sum.inl e : WeightReducedBit R) ≠ Sum.inl e' := by
              exact fun heq => h (Sum.inl.inj heq)
            rw [if_neg hsCheck, if_neg hsBit]
      | inr a =>
          rcases a with ⟨b, j⟩
          by_cases hb : e.1.2 = b
          · subst b
            unfold basisBoundary basisCoboundary primaryBitBoundary
              auxiliaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryCheckIndex_apply_same,
              single_bitIncidenceAt_apply]
            simp only [Pi.single_apply, Sum.inr_ne_inl,
              if_false, zero_add]
            simpa only [Pi.add_apply, Pi.single_apply] using
              (pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
                (F := F) (bitPosition R e) j)
          · unfold basisBoundary basisCoboundary primaryBitBoundary
              auxiliaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryCheckIndex_apply_of_ne R hb,
              single_bitIncidenceAt_apply_of_ne R e hb]
            simp only [Pi.single_apply, Sum.inr_ne_inl, if_false, add_zero]
  | inr a =>
      rcases a with ⟨c, j⟩
      cases q with
      | inl e =>
          by_cases hc : e.1.1 = c
          · subst c
            unfold basisBoundary basisCoboundary auxiliaryBitBoundary
              primaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryBitIndex_apply_same,
              single_checkIncidenceAt_apply]
            simp only [Pi.single_apply, Sum.inr_ne_inl,
              if_false, zero_add]
            simpa only [Pi.add_apply, Pi.single_apply] using
              (pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
                (F := F) (checkPosition R e) j).symm
          · unfold basisBoundary basisCoboundary auxiliaryBitBoundary
              primaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryBitIndex_apply_of_ne R hc,
              single_checkIncidenceAt_apply_of_ne R e hc]
            simp only [Pi.single_apply, Sum.inr_ne_inl, if_false, add_zero]
      | inr a' =>
          simp [basisBoundary, basisCoboundary, auxiliaryBitBoundary,
            auxiliaryCheckCoboundary]

omit [DecidableEq F] in
/-- Every named coboundary basis word is the corresponding row of the actual
weight-reduced boundary operator. -/
theorem transpose_boundary_single (q : WeightReducedCheck R) :
    wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1) =
      basisCoboundary (F := F) R q := by
  unfold boundary
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext i
  exact basisBoundary_apply_eq_basisCoboundary_apply (F := F) R i q

omit [Fintype F] in
theorem HammingWeight_single_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (i : Index) :
    HammingWeight (Pi.single i (1 : F) : Word F Index) ≤ 1 := by
  classical
  rw [HammingWeight_eq_card_hammingSupport]
  calc
    (hammingSupport (Pi.single i (1 : F) : Word F Index)).card ≤
        ({i} : Finset Index).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_singleton]
      by_contra hji
      have hzero : (Pi.single i (1 : F) : Word F Index) j = 0 := by
        rw [Pi.single_eq_of_ne hji]
      simp [hammingSupport, hzero] at hj
    _ = 1 := Finset.card_singleton i

omit [Fintype F] in
theorem HammingWeight_optionalSingle_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (o : Option Index) :
    HammingWeight (optionalSingle (F := F) o) ≤ 1 := by
  cases o with
  | none => simp [optionalSingle]
  | some i => exact HammingWeight_single_le_one (F := F) i

omit [Fintype F] in
/-- Every primary bit participates in at most three weight-reduced checks. -/
theorem HammingWeight_primaryBitBoundary_le_three (e : Incidence R) :
    HammingWeight (primaryBitBoundary (F := F) R e) ≤ 3 := by
  calc
    HammingWeight (primaryBitBoundary (F := F) R e) ≤
        HammingWeight (Pi.single (Sum.inl e) (1 : F) :
          Word F (WeightReducedCheck R)) +
          HammingWeight (optionalSingle (F := F)
            ((pathPrevious (bitPosition R e)).map
              (auxiliaryCheckIndex R e.1.2))) +
          HammingWeight (optionalSingle (F := F)
            ((pathNext (bitPosition R e)).map
              (auxiliaryCheckIndex R e.1.2))) := by
      unfold primaryBitBoundary
      exact (HammingWeight_add_le _ _).trans
        (Nat.add_le_add_right (HammingWeight_add_le _ _) _)
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · exact HammingWeight_single_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
    _ = 3 := by norm_num

omit [Fintype F] in
/-- Every auxiliary bit participates in at most two weight-reduced checks. -/
theorem HammingWeight_auxiliaryBitBoundary_le_two (a : AuxiliaryBit R) :
    HammingWeight (auxiliaryBitBoundary (F := F) R a) ≤ 2 := by
  unfold auxiliaryBitBoundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_single_le_one (F := F) _)
      (HammingWeight_single_le_one (F := F) _))

omit [Fintype F] in
/-- Every primary check acts on at most three weight-reduced bits. -/
theorem HammingWeight_primaryCheckCoboundary_le_three (e : Incidence R) :
    HammingWeight (primaryCheckCoboundary (F := F) R e) ≤ 3 := by
  calc
    HammingWeight (primaryCheckCoboundary (F := F) R e) ≤
        HammingWeight (Pi.single (Sum.inl e) (1 : F) :
          Word F (WeightReducedBit R)) +
          HammingWeight (optionalSingle (F := F)
            ((pathPrevious (checkPosition R e)).map
              (auxiliaryBitIndex R e.1.1))) +
          HammingWeight (optionalSingle (F := F)
            ((pathNext (checkPosition R e)).map
              (auxiliaryBitIndex R e.1.1))) := by
      unfold primaryCheckCoboundary
      exact (HammingWeight_add_le _ _).trans
        (Nat.add_le_add_right (HammingWeight_add_le _ _) _)
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · exact HammingWeight_single_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
    _ = 3 := by norm_num

omit [Fintype F] in
/-- Every auxiliary check acts on at most two weight-reduced bits. -/
theorem HammingWeight_auxiliaryCheckCoboundary_le_two (a : AuxiliaryCheck R) :
    HammingWeight (auxiliaryCheckCoboundary (F := F) R a) ≤ 2 := by
  unfold auxiliaryCheckCoboundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_single_le_one (F := F) _)
      (HammingWeight_single_le_one (F := F) _))

omit [Fintype F] in
/-- Every explicitly described weight-reduced check has weight at most three. -/
theorem HammingWeight_basisCoboundary_le_three (q : WeightReducedCheck R) :
    HammingWeight (basisCoboundary (F := F) R q) ≤ 3 := by
  cases q with
  | inl e => exact HammingWeight_primaryCheckCoboundary_le_three (F := F) R e
  | inr a =>
      exact (HammingWeight_auxiliaryCheckCoboundary_le_two (F := F) R a).trans
        (by norm_num)

/-- Every row of the actual transposed boundary has weight at most three. -/
theorem HammingWeight_transpose_boundary_single_le_three
    (q : WeightReducedCheck R) :
    HammingWeight
      (wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1)) ≤ 3 := by
  rw [transpose_boundary_single]
  exact HammingWeight_basisCoboundary_le_three (F := F) R q

omit [Fintype F] in
/-- Every weight-reduced bit participates in at most three checks. -/
theorem HammingWeight_boundary_single_le_three (i : WeightReducedBit R) :
    HammingWeight (boundary (F := F) R (Pi.single i 1)) ≤ 3 := by
  rw [boundary_single]
  cases i with
  | inl e => exact HammingWeight_primaryBitBoundary_le_three (F := F) R e
  | inr a =>
      exact (HammingWeight_auxiliaryBitBoundary_le_two (F := F) R a).trans
        (by norm_num)

end QEC.Coding.ClassicalWeightReduction
