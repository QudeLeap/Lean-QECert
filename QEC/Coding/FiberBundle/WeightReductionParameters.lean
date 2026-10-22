import QEC.Coding.FiberBundle.WeightReductionDistance
import QEC.Coding.QLDPC.Core
/-!
# Finite parameters of HHO20 fiber-bundle weight reduction

This module bounds the number of cells introduced by the explicit Tanner-path
replacement.  The bounds are derived from the construction indices themselves;
no size or locality conclusion is supplied as input data.
-/

namespace QEC.Coding.FiberBundle

open scoped BigOperators

universe u v

variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)

local notation "R" => baseSupportRelation D

theorem HammingWeight_sum_elim_eq
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B]
    (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) =
      HammingWeight x + HammingWeight y := by
  classical
  let e :
      {s : Sum A B // Sum.elim x y s ≠ 0} ≃
        Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun s =>
        match s with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, ha⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card
        (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem HammingWeight_cycleBoundary_row_le_two
    (n : Nat) [NeZero n] (i : ZMod n) :
    HammingWeight (fun j => cycleBoundary n i j) ≤ 2 := by
  classical
  calc
    HammingWeight (fun j => cycleBoundary n i j) =
        (hammingSupport (fun j => cycleBoundary n i j)).card := rfl
    _ ≤ ({i, i - 1} : Finset (ZMod n)).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] at hj
      by_cases hinc : i = j ∨ i = j + 1
      · rcases hinc with hij | hij
        · simp [hij]
        · have hj : j = i - 1 := by
            calc
              j = (j + 1) - 1 := by simp
              _ = i - 1 := by rw [← hij]
          simp [hj]
      · have hzero : cycleBoundary n i j = 0 := by
          exact if_neg hinc
        exact (hj hzero).elim
    _ ≤ 2 := Finset.card_le_two

theorem HammingWeight_cycleBoundary_col_le_two
    (n : Nat) [NeZero n] (j : ZMod n) :
    HammingWeight (fun i => cycleBoundary n i j) ≤ 2 := by
  classical
  calc
    HammingWeight (fun i => cycleBoundary n i j) =
        (hammingSupport (fun i => cycleBoundary n i j)).card := rfl
    _ ≤ ({j, j + 1} : Finset (ZMod n)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      by_cases hinc : i = j ∨ i = j + 1
      · rcases hinc with hij | hij <;> simp [hij]
      · have hzero : cycleBoundary n i j = 0 := by
          exact if_neg hinc
        exact (hi hzero).elim
    _ ≤ 2 := Finset.card_le_two

theorem HammingWeight_one_fiber_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word F B) (phi : B → Equiv.Perm I) (i : I) :
    HammingWeight
        (fun p : B × I => if i = phi p.1 p.2 then x p.1 else 0) =
      HammingWeight x := by
  classical
  let sourceWord : Word F (B × I) :=
    fun p => if i = phi p.1 p.2 then x p.1 else 0
  let e : {p : B × I // sourceWord p ≠ 0} ≃ {b : B // x b ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.1, by
          by_contra hx
          exact p.2 (by simp [sourceWord, hx])⟩
      invFun := fun b =>
        ⟨(b.1, (phi b.1).symm i), by
          dsimp [sourceWord]
          simpa using b.2⟩
      left_inv := by
        rintro ⟨⟨b, j⟩, hp⟩
        apply Subtype.ext
        change (b, (phi b).symm i) = (b, j)
        apply Prod.ext (show b = b by rfl)
        dsimp [sourceWord] at hp
        by_cases hij : i = phi b j
        · have := congrArg (phi b).symm hij
          simpa using this
        · simp [hij] at hp
      right_inv := by
        rintro ⟨b, hb⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : B × I // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {b : B // x b ≠ 0} := Fintype.card_congr e
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem HammingWeight_fixed_base_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [DecidableEq B] [Fintype I]
    (b : B) (y : Word F I) :
    HammingWeight
        (fun p : B × I => if b = p.1 then y p.2 else 0) =
      HammingWeight y := by
  classical
  let sourceWord : Word F (B × I) :=
    fun p => if b = p.1 then y p.2 else 0
  let e : {p : B × I // sourceWord p ≠ 0} ≃ {i : I // y i ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.2, by
          by_contra hy
          exact p.2 (by simp [sourceWord, hy])⟩
      invFun := fun i =>
        ⟨(b, i.1), by
          dsimp [sourceWord]
          simpa using i.2⟩
      left_inv := by
        rintro ⟨⟨b', i⟩, hp⟩
        apply Subtype.ext
        change (b, i) = (b', i)
        apply Prod.ext
        · dsimp [sourceWord] at hp
          by_cases hbb : b = b'
          · exact hbb
          · simp [hbb] at hp
        · rfl
      right_inv := by
        rintro ⟨i, hi⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : B × I // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {i : I // y i ≠ 0} := Fintype.card_congr e
    _ = HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem HammingWeight_graph_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word F B) (psi : B → I) :
    HammingWeight
        (fun p : B × I => if p.2 = psi p.1 then x p.1 else 0) =
      HammingWeight x := by
  classical
  let sourceWord : Word F (B × I) :=
    fun p => if p.2 = psi p.1 then x p.1 else 0
  let e : {p : B × I // sourceWord p ≠ 0} ≃ {b : B // x b ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.1, by
          by_contra hx
          exact p.2 (by simp [sourceWord, hx])⟩
      invFun := fun b =>
        ⟨(b.1, psi b.1), by
          dsimp [sourceWord]
          simpa using b.2⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, hp⟩
        apply Subtype.ext
        change (b, psi b) = (b, i)
        apply Prod.ext (show b = b by rfl)
        dsimp [sourceWord] at hp
        by_cases hi : i = psi b
        · exact hi.symm
        · simp [hi] at hp
      right_inv := by
        rintro ⟨b, hb⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : B × I // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {b : B // x b ≠ 0} := Fintype.card_congr e
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem wordLinearMapTranspose_matrixToLin_single
    {F Row Col : Type*} [Field F] [Fintype F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M) (Pi.single r 1) =
      fun c => M r c := by
  ext c
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single r]
  · simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _hc' hne
      simp [hne]
    · simp
  · intro x hx
    simp [hx]

theorem wordLinearMapTranspose_single_apply
    {F I K : Type*} [Field F] [Fintype F]
    [Fintype I] [Fintype K]
    (A : Word F I →ₗ[F] Word F K) (k : K) (q : I) :
    wordLinearMapTranspose A (canonicalBasisWord (F := F) k) q =
      A (canonicalBasisWord (F := F) q) k := by
  classical
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  unfold canonicalBasisWord
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hne
    simp [hne]

theorem chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
    {F : Type u} {I K L : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype K] [Fintype L]
    (C : ChainComplexData F (Word F K) (Word F I) (Word F L)) (q : I) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence C).variableSupport q).card =
      HammingWeight
        (C.boundary1 (canonicalBasisWord (F := F) q)) +
      HammingWeight
        (wordLinearMapTranspose C.boundary2
          (canonicalBasisWord (F := F) q)) := by
  classical
  let x := C.boundary1 (canonicalBasisWord (F := F) q)
  let z := wordLinearMapTranspose C.boundary2
    (canonicalBasisWord (F := F) q)
  have hSupport :
      (QEC.QLDPC.chainComplexBoundaryIncidence C).variableSupport q =
        hammingSupport (Sum.elim x z) := by
    ext c
    rw [QEC.QLDPC.CheckIncidence.mem_variableSupport]
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases c with
    | inl k =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, x]
        rw [wordLinearMapTranspose_single_apply]
    | inr l =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, z]
        rw [wordLinearMapTranspose_single_apply]
  rw [hSupport]
  change HammingWeight (Sum.elim x z) =
    HammingWeight x + HammingWeight z
  exact HammingWeight_sum_elim_eq x z

theorem HammingWeight_transpose_boundary1_single_le
    {B F : Nat}
    (a : baseZero) (i : fiberZero)
    (hBase : HammingWeight (fun b => D.baseBoundary a b) ≤ B)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ F) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (a, i) 1)) ≤
      B + F := by
  classical
  rw [boundary1]
  rw [wordLinearMapTranspose_matrixToLin_single]
  have hBlocks :
      (fun c => boundary1Matrix D (a, i) c) =
      Sum.elim
        (fun p : baseOne × fiberZero =>
          if i = (D.connection p.1 a).onZero p.2 then
            D.baseBoundary a p.1 else 0)
        (fun p : baseZero × fiberOne =>
          if a = p.1 then D.fiberBoundary i p.2 else 0) := by
    ext c
    cases c <;> rfl
  rw [hBlocks]
  rw [HammingWeight_sum_elim_eq]
  have hHorizontal :
      HammingWeight
          (fun p : baseOne × fiberZero =>
            if i = (D.connection p.1 a).onZero p.2 then
              D.baseBoundary a p.1 else 0) =
        HammingWeight (fun b => D.baseBoundary a b) :=
    HammingWeight_one_fiber_coordinate_eq
      (fun b => D.baseBoundary a b)
      (fun b => (D.connection b a).onZero) i
  have hVertical :
      HammingWeight
          (fun p : baseZero × fiberOne =>
            if a = p.1 then D.fiberBoundary i p.2 else 0) =
        HammingWeight (fun j => D.fiberBoundary i j) :=
    HammingWeight_fixed_base_coordinate_eq a
      (fun j => D.fiberBoundary i j)
  rw [hHorizontal, hVertical]
  omega

omit [DecidableEq baseZero] [DecidableEq fiberZero] in
theorem HammingWeight_boundary2_single_le
    {B F : Nat}
    (b : baseOne) (j : fiberOne)
    (hBase : HammingWeight (fun a => D.baseBoundary a b) ≤ B)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ F) :
    HammingWeight (boundary2 D (Pi.single (b, j) 1)) ≤ F + B := by
  classical
  rw [boundary2_single]
  have hBlocks :
      (fun p => boundary2Matrix D p (b, j)) =
      Sum.elim
        (fun p : baseOne × fiberZero =>
          if p.1 = b then D.fiberBoundary p.2 j else 0)
        (fun p : baseZero × fiberOne =>
          if p.2 = (D.connection b p.1).onOne j then
            D.baseBoundary p.1 b else 0) := by
    ext p
    cases p <;> rfl
  rw [hBlocks]
  rw [HammingWeight_sum_elim_eq]
  have hHorizontal :
      HammingWeight
          (fun p : baseOne × fiberZero =>
            if p.1 = b then D.fiberBoundary p.2 j else 0) =
        HammingWeight (fun i => D.fiberBoundary i j) := by
    simpa [eq_comm] using
      (HammingWeight_fixed_base_coordinate_eq b
        (fun i => D.fiberBoundary i j))
  have hVertical :
      HammingWeight
          (fun p : baseZero × fiberOne =>
            if p.2 = (D.connection b p.1).onOne j then
              D.baseBoundary p.1 b else 0) =
        HammingWeight (fun a => D.baseBoundary a b) :=
    HammingWeight_graph_coordinate_eq
      (fun a => D.baseBoundary a b)
      (fun a => (D.connection b a).onOne j)
  rw [hHorizontal, hVertical]
  omega

theorem HammingWeight_boundary1_single_inl_eq
    (b : baseOne) (j : fiberZero) :
    HammingWeight (boundary1 D (Pi.single (Sum.inl (b, j)) 1)) =
      HammingWeight (fun a => D.baseBoundary a b) := by
  classical
  rw [boundary1_single_inl]
  exact HammingWeight_graph_coordinate_eq
    (fun a => D.baseBoundary a b)
    (fun a => (D.connection b a).onZero j)

theorem HammingWeight_boundary1_single_inr_eq
    (a : baseZero) (j : fiberOne) :
    HammingWeight (boundary1 D (Pi.single (Sum.inr (a, j)) 1)) =
      HammingWeight (fun i => D.fiberBoundary i j) := by
  classical
  rw [boundary1_single_inr]
  simpa [eq_comm] using
    (HammingWeight_fixed_base_coordinate_eq a
      (fun i => D.fiberBoundary i j))

theorem HammingWeight_transpose_boundary2_single_inl_eq
    (b : baseOne) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inl (b, i)) 1)) =
      HammingWeight (fun j => D.fiberBoundary i j) := by
  classical
  rw [boundary2]
  rw [wordLinearMapTranspose_matrixToLin_single]
  change HammingWeight
      (fun p : baseOne × fiberOne =>
        if b = p.1 then D.fiberBoundary i p.2 else 0) = _
  exact HammingWeight_fixed_base_coordinate_eq b
    (fun j => D.fiberBoundary i j)

theorem HammingWeight_transpose_boundary2_single_inr_eq
    (a : baseZero) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inr (a, j)) 1)) =
      HammingWeight (fun b => D.baseBoundary a b) := by
  classical
  rw [boundary2]
  rw [wordLinearMapTranspose_matrixToLin_single]
  change HammingWeight
      (fun p : baseOne × fiberOne =>
        if j = (D.connection p.1 a).onOne p.2 then
          D.baseBoundary a p.1 else 0) = _
  exact HammingWeight_one_fiber_coordinate_eq
    (fun b => D.baseBoundary a b)
    (fun b => (D.connection b a).onOne) j

theorem HammingWeight_weightReducedData_base_row_le_three
    (q : ClassicalWeightReduction.WeightReducedCheck R) :
    HammingWeight
        (fun b => (weightReducedData D).baseBoundary q b) ≤ 3 := by
  classical
  change HammingWeight
      (fun b => ClassicalWeightReduction.basisBoundary
        (F := ZMod 2) R b q) ≤ 3
  have hRow :
      (fun b => ClassicalWeightReduction.basisBoundary
        (F := ZMod 2) R b q) =
        ClassicalWeightReduction.basisCoboundary (F := ZMod 2) R q := by
    ext b
    exact ClassicalWeightReduction.basisBoundary_apply_eq_basisCoboundary_apply
      (F := ZMod 2) R b q
  rw [hRow]
  exact ClassicalWeightReduction.HammingWeight_basisCoboundary_le_three
    (F := ZMod 2) R q

theorem HammingWeight_weightReducedData_base_col_le_three
    (b : ClassicalWeightReduction.WeightReducedBit R) :
    HammingWeight
        (fun q => (weightReducedData D).baseBoundary q b) ≤ 3 := by
  change HammingWeight
      (ClassicalWeightReduction.basisBoundary (F := ZMod 2) R b) ≤ 3
  rw [← ClassicalWeightReduction.boundary_single]
  exact ClassicalWeightReduction.HammingWeight_boundary_single_le_three
    (F := ZMod 2) R b

theorem boundary1_reducedQubitBasisWord
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    boundary1 (weightReducedData D) (reducedQubitBasisWord D q) =
      fun p => boundary1Matrix (weightReducedData D) p q := by
  classical
  ext p
  unfold boundary1 reducedQubitBasisWord
  change (∑ q', boundary1Matrix (weightReducedData D) p q' *
      (Pi.single q (1 : ZMod 2) : Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne)) q') =
    boundary1Matrix (weightReducedData D) p q
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _hq' hne
    simp [hne]
  · simp

theorem transpose_boundary2_reducedQubitBasisWord
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    wordLinearMapTranspose (boundary2 (weightReducedData D))
        (reducedQubitBasisWord D q) =
      fun p => boundary2Matrix (weightReducedData D) q p := by
  classical
  ext p
  unfold wordLinearMapTranspose reducedQubitBasisWord boundary2
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single q]
  · rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · simp
    · intro p' _hp' hne
      simp [hne]
    · simp
  · intro q' hne
    simp [hne]

theorem HammingWeight_boundary1_reducedQubitBasisWord_inl_eq
    (b : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inl (b, i)))) =
      HammingWeight
        (fun a => (weightReducedData D).baseBoundary a b) := by
  classical
  rw [boundary1_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedCheck R × fiberZero =>
        if p.2 = ((weightReducedData D).connection b p.1).onZero i then
          (weightReducedData D).baseBoundary p.1 b else 0) = _
  exact HammingWeight_graph_coordinate_eq
    (fun a => (weightReducedData D).baseBoundary a b)
    (fun a => ((weightReducedData D).connection b a).onZero i)

theorem HammingWeight_boundary1_reducedQubitBasisWord_inr_eq
    (a : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    HammingWeight
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inr (a, j)))) =
      HammingWeight (fun i => D.fiberBoundary i j) := by
  classical
  rw [boundary1_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedCheck R × fiberZero =>
        if p.1 = a then D.fiberBoundary p.2 j else 0) = _
  simpa [eq_comm] using
    (HammingWeight_fixed_base_coordinate_eq a
      (fun i => D.fiberBoundary i j))

theorem HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
    (b : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inl (b, i)))) =
      HammingWeight (fun j => D.fiberBoundary i j) := by
  classical
  rw [transpose_boundary2_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedBit R × fiberOne =>
        if b = p.1 then D.fiberBoundary i p.2 else 0) = _
  exact HammingWeight_fixed_base_coordinate_eq b
    (fun j => D.fiberBoundary i j)

theorem HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
    (a : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inr (a, j)))) =
      HammingWeight
        (fun b => (weightReducedData D).baseBoundary a b) := by
  classical
  rw [transpose_boundary2_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedBit R × fiberOne =>
        if j = ((weightReducedData D).connection p.1 a).onOne p.2 then
          (weightReducedData D).baseBoundary a p.1 else 0) = _
  exact HammingWeight_one_fiber_coordinate_eq
    (fun b => (weightReducedData D).baseBoundary a b)
    (fun b => ((weightReducedData D).connection b a).onOne) j

/-- Every X-check row of a weight-reduced bundle has weight at most five when
the fiber boundary has row weight at most two. -/
theorem HammingWeight_transpose_boundary1_weightReducedData_single_le_five
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (weightReducedData D))
          (Pi.single (q, i) 1)) ≤ 5 := by
  apply (HammingWeight_transpose_boundary1_single_le
    (weightReducedData D) (B := 3) (F := 2) q i
    (HammingWeight_weightReducedData_base_row_le_three D q) hFiber).trans
  omega

/-- Canonical-basis form of the reduced-bundle X-check bound. -/
theorem HammingWeight_transpose_boundary1_weightReducedData_canonical_le_five
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (weightReducedData D))
          (canonicalBasisWord (F := ZMod 2) (q, i))) ≤ 5 := by
  classical
  have hBasis : canonicalBasisWord (F := ZMod 2) (q, i) =
      (Pi.single (q, i) 1 : Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero)) := by
    ext x
    by_cases h : (q, i) = x
    · subst x
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, h]
  rw [hBasis]
  exact HammingWeight_transpose_boundary1_weightReducedData_single_le_five
    D q i hFiber

/-- Every Z-check row of a weight-reduced bundle has weight at most five when
the fiber boundary has column weight at most two. -/
theorem HammingWeight_boundary2_weightReducedData_single_le_five
    (b : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary2 (weightReducedData D) (Pi.single (b, j) 1)) ≤ 5 := by
  apply (HammingWeight_boundary2_single_le
    (weightReducedData D) (B := 3) (F := 2) b j
    (HammingWeight_weightReducedData_base_col_le_three D b) hFiber).trans
  omega

/-- Canonical-basis form of the reduced-bundle Z-check bound. -/
theorem HammingWeight_boundary2_weightReducedData_canonical_le_five
    (b : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary2 (weightReducedData D)
          (canonicalBasisWord (F := ZMod 2) (b, j))) ≤ 5 := by
  classical
  have hBasis : canonicalBasisWord (F := ZMod 2) (b, j) =
      (Pi.single (b, j) 1 : Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne)) := by
    ext x
    by_cases h : (b, j) = x
    · subst x
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, h]
  rw [hBasis]
  exact HammingWeight_boundary2_weightReducedData_single_le_five
    D b j hFiber

/-- Every reduced-bundle qubit participates in at most five checks in total
when both fiber-boundary row and column weights are at most two. -/
theorem HammingWeight_boundary_columns_weightReducedData_le_five
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) ≤ 5 := by
  cases q with
  | inl q =>
      rcases q with ⟨b, i⟩
      rw [HammingWeight_boundary1_reducedQubitBasisWord_inl_eq D b i]
      rw [HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
        D b i]
      have hBase := HammingWeight_weightReducedData_base_col_le_three D b
      have hFiber := hFiberRow i
      omega
  | inr q =>
      rcases q with ⟨a, j⟩
      rw [HammingWeight_boundary1_reducedQubitBasisWord_inr_eq D a j]
      rw [HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
        D a j]
      have hFiber := hFiberCol j
      have hBase := HammingWeight_weightReducedData_base_row_le_three D a
      omega

theorem chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card =
      HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) := by
  classical
  rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
    (chainComplex (weightReducedData D)) q]
  unfold chainComplex reducedQubitBasisWord
  rfl

theorem chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card ≤ 5 := by
  rw [chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq D q]
  exact HammingWeight_boundary_columns_weightReducedData_le_five
    D q hFiberRow hFiberCol

theorem card_incidence_eq_sum_bitNeighbor :
    Fintype.card (ClassicalWeightReduction.Incidence R) =
      ∑ b : baseOne,
        Fintype.card (ClassicalWeightReduction.BitNeighbor R b) := by
  rw [Fintype.card_congr (incidenceBitPositionEquiv D)]
  simp [ClassicalWeightReduction.BitPositionSigma]

theorem card_incidence_le_card_baseOne_mul
    {L : Nat}
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L) :
    Fintype.card (ClassicalWeightReduction.Incidence R) ≤
      Fintype.card baseOne * L := by
  rw [card_incidence_eq_sum_bitNeighbor D]
  calc
    (∑ b : baseOne,
        Fintype.card (ClassicalWeightReduction.BitNeighbor R b)) ≤
        ∑ _b : baseOne, L := by
      apply Finset.sum_le_sum
      intro b _hb
      exact hBitDegree b
    _ = Fintype.card baseOne * L := by simp

theorem card_auxiliaryCheck_le_card_incidence :
    Fintype.card (ClassicalWeightReduction.AuxiliaryCheck R) ≤
      Fintype.card (ClassicalWeightReduction.Incidence R) := by
  rw [card_incidence_eq_sum_bitNeighbor D]
  simp only [ClassicalWeightReduction.AuxiliaryCheck,
    Fintype.card_sigma, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro b _hb
  omega

theorem card_auxiliaryBit_le_card_incidence :
    Fintype.card (ClassicalWeightReduction.AuxiliaryBit R) ≤
      Fintype.card (ClassicalWeightReduction.Incidence R) := by
  classical
  let incidenceCheckPositionEquiv :
      ClassicalWeightReduction.Incidence R ≃
        (Σ c : baseZero,
          Fin (Fintype.card
            (ClassicalWeightReduction.CheckNeighbor R c))) :=
    { toFun := fun e =>
        ⟨e.1.1, ClassicalWeightReduction.checkPosition R e⟩
      invFun := fun s =>
        ClassicalWeightReduction.checkIncidenceAt R s.1 s.2
      left_inv := ClassicalWeightReduction.checkIncidenceAt_checkPosition R
      right_inv := by
        rintro ⟨c, i⟩
        change (⟨c,
          ClassicalWeightReduction.checkPosition R
            (ClassicalWeightReduction.checkIncidenceAt R c i)⟩ :
              Σ c : baseZero,
                Fin (Fintype.card
                  (ClassicalWeightReduction.CheckNeighbor R c))) = ⟨c, i⟩
        apply Sigma.ext (show c = c by rfl)
        simp }
  rw [Fintype.card_congr incidenceCheckPositionEquiv]
  simp only [ClassicalWeightReduction.AuxiliaryBit,
    Fintype.card_sigma, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro c _hc
  omega

theorem card_weightReducedCheck_le_two_mul_incidence :
    Fintype.card (ClassicalWeightReduction.WeightReducedCheck R) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) := by
  rw [show Fintype.card
      (ClassicalWeightReduction.WeightReducedCheck R) =
        Fintype.card (ClassicalWeightReduction.Incidence R) +
          Fintype.card (ClassicalWeightReduction.AuxiliaryCheck R) by simp]
  have hAux := card_auxiliaryCheck_le_card_incidence D
  omega

theorem card_weightReducedBit_le_two_mul_incidence :
    Fintype.card (ClassicalWeightReduction.WeightReducedBit R) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) := by
  rw [show Fintype.card
      (ClassicalWeightReduction.WeightReducedBit R) =
        Fintype.card (ClassicalWeightReduction.Incidence R) +
          Fintype.card (ClassicalWeightReduction.AuxiliaryBit R) by simp]
  have hAux := card_auxiliaryBit_le_card_incidence D
  omega

/-- The reduced bundle has at most two incidence copies in each of its two
middle-chain blocks. -/
theorem card_qubitIndex_weightReduced_le :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by
  rw [card_qubitIndex]
  have hBit := card_weightReducedBit_le_two_mul_incidence D
  have hCheck := card_weightReducedCheck_le_two_mul_incidence D
  nlinarith

theorem card_qubitIndex_weightReduced_le_of_bitDegree
    {L : Nat}
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L) :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * (Fintype.card baseOne * L) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by
  exact (card_qubitIndex_weightReduced_le D).trans
    (Nat.mul_le_mul_right
      (Fintype.card fiberZero + Fintype.card fiberOne)
      (Nat.mul_le_mul_left 2
        (card_incidence_le_card_baseOne_mul D hBitDegree)))

namespace RandomBase

/-- The HHO20 cycle fiber makes every X-check of the weight-reduced random
bundle have weight at most five. -/
theorem HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (i : ZMod (ell * ell)) :
    HammingWeight
        (wordLinearMapTranspose
          (boundary1 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (Pi.single (q, i) 1)) ≤ 5 := by
  apply HammingWeight_transpose_boundary1_weightReducedData_single_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) q i
  exact HammingWeight_cycleBoundary_row_le_two (ell * ell) i

/-- Canonical-basis form of the construction-owned HHO20 X-check bound. -/
theorem HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_canonical_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (i : ZMod (ell * ell)) :
    HammingWeight
        (wordLinearMapTranspose
          (boundary1 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (canonicalBasisWord (F := ZMod 2) (q, i))) ≤ 5 := by
  apply HammingWeight_transpose_boundary1_weightReducedData_canonical_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) q i
  exact HammingWeight_cycleBoundary_row_le_two (ell * ell) i

/-- The HHO20 cycle fiber makes every Z-check of the weight-reduced random
bundle have weight at most five. -/
theorem HammingWeight_boundary2_weightReduced_randomFiberBundleData_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : ClassicalWeightReduction.WeightReducedBit
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (j : ZMod (ell * ell)) :
    HammingWeight
        (boundary2 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (Pi.single (b, j) 1)) ≤ 5 := by
  apply HammingWeight_boundary2_weightReducedData_single_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) b j
  exact HammingWeight_cycleBoundary_col_le_two (ell * ell) j

/-- Canonical-basis form of the construction-owned HHO20 Z-check bound. -/
theorem HammingWeight_boundary2_weightReduced_randomFiberBundleData_canonical_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : ClassicalWeightReduction.WeightReducedBit
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (j : ZMod (ell * ell)) :
    HammingWeight
        (boundary2 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (canonicalBasisWord (F := ZMod 2) (b, j))) ≤ 5 := by
  apply HammingWeight_boundary2_weightReducedData_canonical_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) b j
  exact HammingWeight_cycleBoundary_col_le_two (ell * ell) j

/-- Every physical qubit of the weight-reduced HHO20 random bundle is incident
to at most five X- and Z-checks in total. -/
theorem HammingWeight_boundary_columns_weightReduced_randomFiberBundleData_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ClassicalWeightReduction.WeightReducedBit
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ZMod (ell * ell)) (ZMod (ell * ell))) :
    HammingWeight
        (boundary1 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (boundary2 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) ≤ 5 := by
  apply HammingWeight_boundary_columns_weightReducedData_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) q
  · exact fun i => HammingWeight_cycleBoundary_row_le_two (ell * ell) i
  · exact fun j => HammingWeight_cycleBoundary_col_le_two (ell * ell) j

/-- The actual HHO20 chain-complex incidence has variable degree at most five,
not merely a matrix-column proxy for that degree. -/
theorem chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ClassicalWeightReduction.WeightReducedBit
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ZMod (ell * ell)) (ZMod (ell * ell))) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample)))).variableSupport q).card ≤ 5 := by
  apply chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) q
  · exact fun i => HammingWeight_cycleBoundary_row_le_two (ell * ell) i
  · exact fun j => HammingWeight_cycleBoundary_col_le_two (ell * ell) j

/-- Fully-good HHO20 samples incur only the explicit degree-window factor in
the physical-qubit count under weight reduction. -/
theorem card_qubitIndex_weightReduced_randomFiberBundleData_le
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck
            (baseSupportRelation
              (RandomTwist.fiberBundleData baseSample twistSample)))
          (ClassicalWeightReduction.WeightReducedBit
            (baseSupportRelation
              (RandomTwist.fiberBundleData baseSample twistSample)))
          (ZMod (ell * ell)) (ZMod (ell * ell))) ≤
      1616 * r * Delta * (ell * ell) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  apply (card_qubitIndex_weightReduced_le_of_bitDegree
    D (L := 101 * Delta) ?_).trans
  · simp only [Fintype.card_fin, ZMod.card]
    ring_nf
    omega
  · intro b
    have hp :
        (fun c => baseSupportRelation D c b) =
          fun c => incidenceRelation baseSample c b := by
      funext c
      exact propext
        (baseSupportRelation_randomFiberBundleData_iff
          baseSample twistSample c b)
    rw [Fintype.card_congr (Equiv.subtypeEquivProp hp)]
    exact bitNeighbor_card_le_of_degreeWindows
      baseSample hGood.1.1 b

end RandomBase

end QEC.Coding.FiberBundle
