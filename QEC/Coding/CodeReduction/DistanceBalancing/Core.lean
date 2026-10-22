import QEC.Coding.ChainComplex.Duality
import QEC.Coding.CodeReduction.Classical.Distance
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# EKZ20 finite distance-balancing product

This module implements the finite-coordinate product used by
Evra--Kaufman--Zémor to balance the two distances of a binary quantum code.
The construction takes a three-term binary chain complex and a two-term
classical boundary matrix.  Its boundary maps are given block-by-block, and
their composition is proved to vanish from the source square-zero identity.

No matrix, rank, distance, or locality conclusion is accepted as part of the
constructed output.
-/

namespace QEC.Coding.DistanceBalancing

universe u

open scoped BigOperators

/-- Finite binary matrix data for a three-term complex and a classical
one-boundary complex. -/
structure Data
    (xZero xOne xTwo classicalBit classicalCheck : Type u)
    [Fintype xZero] [Fintype xOne] [Fintype xTwo]
    [Fintype classicalBit] [Fintype classicalCheck] where
  xBoundary1 : Matrix xZero xOne (ZMod 2)
  xBoundary2 : Matrix xOne xTwo (ZMod 2)
  classicalBoundary : Matrix classicalCheck classicalBit (ZMod 2)
  x_boundary_squared : xBoundary1 * xBoundary2 = 0

/-- Every nonzero word in the kernel of a classical parity-check matrix has
Hamming weight at least `d`. -/
def ClassicalDistanceAtLeast
    {classicalBit classicalCheck : Type u}
    [Fintype classicalBit] [DecidableEq classicalBit]
    [Fintype classicalCheck]
    (H : Matrix classicalCheck classicalBit (ZMod 2))
    (d : Nat) : Prop :=
  ∀ w : Word (ZMod 2) classicalBit,
    Matrix.toLin' H w = 0 → w ≠ 0 → d ≤ HammingWeight w

/-- Derive all product matrices from honest linear boundary maps.  This is the
entry point used by the HHO20 instantiation, so no external matrix
representation is required. -/
noncomputable def Data.ofComplexes
    {xZero xOne xTwo classicalBit classicalCheck : Type u}
    [Fintype xZero] [DecidableEq xZero]
    [Fintype xOne] [DecidableEq xOne]
    [Fintype xTwo] [DecidableEq xTwo]
    [Fintype classicalBit] [DecidableEq classicalBit]
    [Fintype classicalCheck] [DecidableEq classicalCheck]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    Data xZero xOne xTwo classicalBit classicalCheck where
  xBoundary1 := LinearMap.toMatrix' X.boundary1
  xBoundary2 := LinearMap.toMatrix' X.boundary2
  classicalBoundary := LinearMap.toMatrix' Y
  x_boundary_squared := by
    rw [← LinearMap.toMatrix'_comp]
    rw [X.boundary_squared]
    simp

/-- Degree zero of the truncated EKZ product. -/
abbrev C0Index (xZero xOne classicalBit classicalCheck : Type u) :=
  Sum (xZero × classicalBit) (xOne × classicalCheck)

/-- Degree one (physical qubits) of the truncated EKZ product. -/
abbrev QubitIndex (xOne xTwo classicalBit classicalCheck : Type u) :=
  Sum (xOne × classicalBit) (xTwo × classicalCheck)

/-- Degree two of the truncated EKZ product. -/
abbrev C2Index (xTwo classicalBit : Type u) := xTwo × classicalBit

variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

/-- A matrix right inverse for the classical boundary. -/
def IsClassicalRightInverse
    (S : Matrix classicalBit classicalCheck (ZMod 2)) : Prop :=
  D.classicalBoundary * S = 1

/-- The source three-term complex encoded by the two `X` matrices in `D`. -/
noncomputable def sourceChainComplex :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo) where
  boundary1 := Matrix.toLin' D.xBoundary1
  boundary2 := Matrix.toLin' D.xBoundary2
  boundary_squared := by
    change (Matrix.toLin' D.xBoundary1).comp
      (Matrix.toLin' D.xBoundary2) = 0
    rw [← Matrix.toLin'_mul]
    rw [D.x_boundary_squared]
    simp

@[simp]
theorem sourceChainComplex_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    sourceChainComplex (Data.ofComplexes X Y) = X := by
  cases X
  simp [sourceChainComplex, Data.ofComplexes, Matrix.toLin'_toMatrix']

@[simp]
theorem classicalBoundary_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    (Data.ofComplexes X Y).classicalBoundary = LinearMap.toMatrix' Y := rfl

/-- First boundary matrix of the EKZ truncated product. -/
def boundary1Matrix :
    Matrix
      (C0Index xZero xOne classicalBit classicalCheck)
      (QubitIndex xOne xTwo classicalBit classicalCheck)
      (ZMod 2) :=
  fun r c =>
    match r, c with
    | Sum.inl (x0, a), Sum.inl (x1, a') =>
        if a = a' then D.xBoundary1 x0 x1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr (x1, b), Sum.inl (x1', a) =>
        if x1 = x1' then D.classicalBoundary b a else 0
    | Sum.inr (x1, b), Sum.inr (x2, b') =>
        if b = b' then D.xBoundary2 x1 x2 else 0

/-- Second boundary matrix of the EKZ truncated product. -/
def boundary2Matrix :
    Matrix
      (QubitIndex xOne xTwo classicalBit classicalCheck)
      (C2Index xTwo classicalBit)
      (ZMod 2) :=
  fun r c =>
    match r, c with
    | Sum.inl (x1, a'), (x2, a) =>
        if a' = a then D.xBoundary2 x1 x2 else 0
    | Sum.inr (x2', b), (x2, a) =>
        if x2' = x2 then D.classicalBoundary b a else 0

@[simp]
theorem boundary1Matrix_inl_inl
    (x0 : xZero) (a a' : classicalBit) (x1 : xOne) :
    boundary1Matrix D (Sum.inl (x0, a)) (Sum.inl (x1, a')) =
      if a = a' then D.xBoundary1 x0 x1 else 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inl_inr
    (x0 : xZero) (a : classicalBit)
    (x2 : xTwo) (b : classicalCheck) :
    boundary1Matrix D (Sum.inl (x0, a)) (Sum.inr (x2, b)) = 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inr_inl
    (x1 x1' : xOne) (b : classicalCheck) (a : classicalBit) :
    boundary1Matrix D (Sum.inr (x1, b)) (Sum.inl (x1', a)) =
      if x1 = x1' then D.classicalBoundary b a else 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inr_inr
    (x1 : xOne) (b b' : classicalCheck) (x2 : xTwo) :
    boundary1Matrix D (Sum.inr (x1, b)) (Sum.inr (x2, b')) =
      if b = b' then D.xBoundary2 x1 x2 else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inl
    (x1 : xOne) (a' a : classicalBit) (x2 : xTwo) :
    boundary2Matrix D (Sum.inl (x1, a')) (x2, a) =
      if a' = a then D.xBoundary2 x1 x2 else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inr
    (x2' x2 : xTwo) (b : classicalCheck) (a : classicalBit) :
    boundary2Matrix D (Sum.inr (x2', b)) (x2, a) =
      if x2' = x2 then D.classicalBoundary b a else 0 := by
  rfl

/-- The two EKZ block boundary matrices compose to zero. -/
theorem boundary1Matrix_mul_boundary2Matrix :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext r c
  rcases c with ⟨x2, a⟩
  cases r with
  | inl r =>
      rcases r with ⟨x0, a0⟩
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type, boundary1Matrix_inl_inl,
        boundary1Matrix_inl_inr, boundary2Matrix_inl,
        boundary2Matrix_inr, zero_mul, Finset.sum_const_zero, add_zero]
      by_cases haa : a0 = a
      · subst a0
        simp
        have hsquare := congrFun (congrFun D.x_boundary_squared x0) x2
        simpa [Matrix.mul_apply] using hsquare
      · simp [haa]
  | inr r =>
      rcases r with ⟨x1, b⟩
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type, boundary1Matrix_inr_inl,
        boundary1Matrix_inr_inr, boundary2Matrix_inl,
        boundary2Matrix_inr]
      simp
      rw [mul_comm (D.classicalBoundary b a)]
      exact ZModModule.add_self _

/-- First boundary linear map of the EKZ product. -/
noncomputable def boundary1 :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) →ₗ[ZMod 2]
      Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck) :=
  Matrix.toLin' (boundary1Matrix D)

/-- Second boundary linear map of the EKZ product. -/
noncomputable def boundary2 :
    Word (ZMod 2) (C2Index xTwo classicalBit) →ₗ[ZMod 2]
      Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Matrix.toLin' (boundary2Matrix D)

theorem boundary_squared :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp

/-- Honest three-term chain complex underlying the EKZ product code. -/
noncomputable def chainComplex :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck))
      (Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck))
      (Word (ZMod 2) (C2Index xTwo classicalBit)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D

/-! ## Coordinate slice formulas -/

/-- The `X₁ ⊗ A` block of a product middle-chain word, sliced at `a`. -/
def xOneBitSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) : Word (ZMod 2) xOne :=
  fun x1 => z (Sum.inl (x1, a))

/-- The `X₂ ⊗ B` block of a product middle-chain word, sliced at `b`. -/
def xTwoCheckSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (b : classicalCheck) : Word (ZMod 2) xTwo :=
  fun x2 => z (Sum.inr (x2, b))

/-- A product degree-two word, sliced at a classical bit coordinate. -/
def xTwoBitSlice
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (a : classicalBit) : Word (ZMod 2) xTwo :=
  fun x2 => w (x2, a)

/-- Contract the first product block against a classical-bit word. -/
noncomputable def sourceCochainContraction
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) : Word (ZMod 2) xOne :=
  ∑ a : classicalBit, c a • xOneBitSlice x a

theorem boundary1_apply_inl
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x0 : xZero) (a : classicalBit) :
    boundary1 D z (Sum.inl (x0, a)) =
      ∑ x1 : xOne,
        D.xBoundary1 x0 x1 * xOneBitSlice z a x1 := by
  rw [boundary1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  simp [Fintype.sum_prod_type, xOneBitSlice]

theorem boundary1_apply_inr
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x1 : xOne) (b : classicalCheck) :
    boundary1 D z (Sum.inr (x1, b)) =
      (∑ a : classicalBit,
        D.classicalBoundary b a * xOneBitSlice z a x1) +
      ∑ x2 : xTwo,
        D.xBoundary2 x1 x2 * xTwoCheckSlice z b x2 := by
  rw [boundary1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  simp [Fintype.sum_prod_type, xOneBitSlice, xTwoCheckSlice]

theorem boundary2_apply_inl
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (x1 : xOne) (a : classicalBit) :
    boundary2 D w (Sum.inl (x1, a)) =
      ∑ x2 : xTwo,
        D.xBoundary2 x1 x2 * xTwoBitSlice w a x2 := by
  rw [boundary2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp [Fintype.sum_prod_type, xTwoBitSlice]

theorem boundary2_apply_inr
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (x2 : xTwo) (b : classicalCheck) :
    boundary2 D w (Sum.inr (x2, b)) =
      ∑ a : classicalBit,
        D.classicalBoundary b a * xTwoBitSlice w a x2 := by
  rw [boundary2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp [Fintype.sum_prod_type, xTwoBitSlice]

/-- Coordinate formula for the transpose of the product's second boundary. -/
theorem transpose_boundary2_apply
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x2 : xTwo) (a : classicalBit) :
    wordLinearMapTranspose (boundary2 D) x (x2, a) =
      (∑ x1 : xOne,
        D.xBoundary2 x1 x2 * xOneBitSlice x a x1) +
      ∑ b : classicalCheck,
        D.classicalBoundary b a * xTwoCheckSlice x b x2 := by
  rw [boundary2, wordLinearMapTranspose_toLin'_apply,
    Fintype.sum_sum_type]
  simp [boundary2Matrix, Fintype.sum_prod_type,
    xOneBitSlice, xTwoCheckSlice]
  simp only [mul_comm]

theorem transpose_boundary1_apply_inl
    (u : Word (ZMod 2)
      (C0Index xZero xOne classicalBit classicalCheck))
    (x1 : xOne) (a : classicalBit) :
    wordLinearMapTranspose (boundary1 D) u (Sum.inl (x1, a)) =
      (∑ x0 : xZero,
        D.xBoundary1 x0 x1 * u (Sum.inl (x0, a))) +
      ∑ b : classicalCheck,
        D.classicalBoundary b a * u (Sum.inr (x1, b)) := by
  rw [boundary1, wordLinearMapTranspose_toLin'_apply,
    Fintype.sum_sum_type]
  simp [boundary1Matrix, Fintype.sum_prod_type]
  simp only [mul_comm]

theorem transpose_boundary1_apply_inr
    (u : Word (ZMod 2)
      (C0Index xZero xOne classicalBit classicalCheck))
    (x2 : xTwo) (b : classicalCheck) :
    wordLinearMapTranspose (boundary1 D) u (Sum.inr (x2, b)) =
      ∑ x1 : xOne,
        D.xBoundary2 x1 x2 * u (Sum.inr (x1, b)) := by
  rw [boundary1, wordLinearMapTranspose_toLin'_apply,
    Fintype.sum_sum_type]
  simp [boundary1Matrix, Fintype.sum_prod_type]
  simp only [mul_comm]

/-- Contracting a product cocycle against a classical codeword produces a
source cocycle. -/
theorem sourceCochainContraction_mem_middleCocycleCode
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (c : Word (ZMod 2) classicalBit)
    (hc : Matrix.toLin' D.classicalBoundary c = 0) :
    sourceCochainContraction x c ∈
      (sourceChainComplex D).middleCocycleCode.carrier := by
  rw [(sourceChainComplex D).mem_middleCocycleCode_iff]
  ext x2
  have hxZero := ((chainComplex D).mem_middleCocycleCode_iff x).1 hx
  change wordLinearMapTranspose (boundary2 D) x = 0 at hxZero
  have hAt : ∀ a : classicalBit,
      (∑ x1 : xOne,
          D.xBoundary2 x1 x2 * xOneBitSlice x a x1) =
        ∑ b : classicalCheck,
          D.classicalBoundary b a * xTwoCheckSlice x b x2 := by
    intro a
    have h := congrFun hxZero (x2, a)
    simp only [Pi.zero_apply] at h
    rw [transpose_boundary2_apply] at h
    have hNeg := eq_neg_of_add_eq_zero_left h
    simpa [ZModModule.neg_eq_self] using hNeg
  change wordLinearMapTranspose (Matrix.toLin' D.xBoundary2)
    (sourceCochainContraction x c) x2 = 0
  rw [wordLinearMapTranspose_toLin'_apply]
  simp only [sourceCochainContraction, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x1 : xOne,
        (∑ a : classicalBit, c a * xOneBitSlice x a x1) *
          D.xBoundary2 x1 x2) =
        ∑ a : classicalBit, c a *
          (∑ x1 : xOne,
            D.xBoundary2 x1 x2 * xOneBitSlice x a x1) := by
      simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = ∑ b : classicalCheck,
        (Matrix.toLin' D.classicalBoundary c b) *
          xTwoCheckSlice x b x2 := by
      simp_rw [hAt]
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = 0 := by rw [hc]; simp

/-- Contraction cannot weigh more than all first-block slices together. -/
theorem HammingWeight_sourceCochainContraction_le
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) :
    HammingWeight (sourceCochainContraction x c) ≤
      ∑ a : classicalBit, HammingWeight (xOneBitSlice x a) := by
  apply (HammingWeight_finset_sum_le Finset.univ
    (fun a => c a • xOneBitSlice x a)).trans
  apply Finset.sum_le_sum
  intro a _ha
  exact HammingWeight_smul_le (c a) (xOneBitSlice x a)

theorem sum_HammingWeight_xOneBitSlice_le_product
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    (∑ a : classicalBit, HammingWeight (xOneBitSlice x a)) ≤
      HammingWeight x := by
  classical
  let f : (Σ a : classicalBit,
      {x1 : xOne // xOneBitSlice x a x1 ≠ 0}) →
      {q : QubitIndex xOne xTwo classicalBit classicalCheck // x q ≠ 0} :=
    fun p => ⟨Sum.inl (p.2.1, p.1), p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ⟨x1, hx1⟩⟩ ⟨a', ⟨x1', hx1'⟩⟩ h
    have hp := Sum.inl.inj (congrArg (fun q => q.1) h)
    have ha : a = a' := congrArg Prod.snd hp
    subst a'
    have hx : x1 = x1' := congrArg Prod.fst hp
    subst x1'
    rfl
  calc
    (∑ a : classicalBit, HammingWeight (xOneBitSlice x a)) =
        Fintype.card (Σ a : classicalBit,
          {x1 : xOne // xOneBitSlice x a x1 ≠ 0}) := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ ≤ Fintype.card
        {q : QubitIndex xOne xTwo classicalBit classicalCheck // x q ≠ 0} :=
      Fintype.card_le_of_injective f hf
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- The standard projection of a classical basis word onto the kernel of a
surjective parity-check map, using a chosen right inverse. -/
noncomputable def classicalKernelProjectionWord
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (a : classicalBit) : Word (ZMod 2) classicalBit :=
  Pi.single a 1 + Matrix.toLin' S
    (Matrix.toLin' D.classicalBoundary (Pi.single a 1))

theorem classicalKernelProjectionWord_mem_kernel
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (a : classicalBit) :
    Matrix.toLin' D.classicalBoundary
      (classicalKernelProjectionWord D S a) = 0 := by
  rw [classicalKernelProjectionWord, map_add]
  have hComp :
      (Matrix.toLin' D.classicalBoundary).comp (Matrix.toLin' S) =
        LinearMap.id := by
    rw [← Matrix.toLin'_mul]
    change D.classicalBoundary * S = 1 at hS
    rw [hS]
    simp
  change Matrix.toLin' D.classicalBoundary (Pi.single a 1) +
    ((Matrix.toLin' D.classicalBoundary).comp (Matrix.toLin' S))
      (Matrix.toLin' D.classicalBoundary (Pi.single a 1)) = 0
  rw [hComp]
  exact ZModModule.add_self _

/-- Source one-cochain obtained by contracting against one column of the
chosen classical right inverse. -/
noncomputable def sourceCochainLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (b : classicalCheck) : Word (ZMod 2) xOne :=
  sourceCochainContraction x (fun a => S a b)

theorem sourceCochainContraction_add
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c c' : Word (ZMod 2) classicalBit) :
    sourceCochainContraction x (c + c') =
      sourceCochainContraction x c + sourceCochainContraction x c' := by
  ext x1
  simp [sourceCochainContraction, Finset.sum_add_distrib, add_mul]

theorem sourceCochainContraction_single
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    sourceCochainContraction x (Pi.single a 1) = xOneBitSlice x a := by
  classical
  ext x1
  simp only [sourceCochainContraction, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro a' hne
    simp [hne]

theorem sourceCochainContraction_rightInverseImage
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    sourceCochainContraction x
        (Matrix.toLin' S
          (Matrix.toLin' D.classicalBoundary (Pi.single a 1))) =
      ∑ b : classicalCheck,
        D.classicalBoundary b a • sourceCochainLift S x b := by
  ext x1
  simp only [sourceCochainContraction, sourceCochainLift,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  exact Finset.sum_comm

/-- The projected slice is the contraction against a kernel-projected basis
word. -/
noncomputable def projectedSourceCochain
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) : Word (ZMod 2) xOne :=
  sourceCochainContraction x (classicalKernelProjectionWord D S a)

theorem projectedSourceCochain_eq
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    projectedSourceCochain D S x a =
      xOneBitSlice x a +
        ∑ b : classicalCheck,
          D.classicalBoundary b a • sourceCochainLift S x b := by
  rw [projectedSourceCochain, classicalKernelProjectionWord,
    sourceCochainContraction_add,
    sourceCochainContraction_single,
    sourceCochainContraction_rightInverseImage D]

theorem projectedSourceCochain_mem_middleCocycleCode
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (a : classicalBit) :
    projectedSourceCochain D S x a ∈
      (sourceChainComplex D).middleCocycleCode.carrier :=
  sourceCochainContraction_mem_middleCocycleCode D x hx
    (classicalKernelProjectionWord D S a)
    (classicalKernelProjectionWord_mem_kernel D S hS a)

theorem projectedSourceCochain_mem_firstCoboundary_of_weight_lt
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hWeight : HammingWeight x < d)
    (a : classicalBit) :
    projectedSourceCochain D S x a ∈
      (sourceChainComplex D).firstCoboundaryCheckCode.carrier := by
  by_contra hNonboundary
  have hLower := hDistance (projectedSourceCochain D S x a)
    (projectedSourceCochain_mem_middleCocycleCode D S hS x hx a)
    hNonboundary
  have hUpper : HammingWeight (projectedSourceCochain D S x a) ≤
      HammingWeight x := by
    change HammingWeight
      (sourceCochainContraction x (classicalKernelProjectionWord D S a)) ≤
        HammingWeight x
    exact (HammingWeight_sourceCochainContraction_le
      x (classicalKernelProjectionWord D S a)).trans
        (sum_HammingWeight_xOneBitSlice_le_product x)
  omega

/-- The lifted source cochain has exactly the required second-block
coboundary, by the right-inverse identity. -/
theorem transpose_sourceBoundary2_sourceCochainLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (b : classicalCheck) :
    wordLinearMapTranspose (sourceChainComplex D).boundary2
      (sourceCochainLift S x b) = xTwoCheckSlice x b := by
  ext x2
  have hxZero := ((chainComplex D).mem_middleCocycleCode_iff x).1 hx
  change wordLinearMapTranspose (boundary2 D) x = 0 at hxZero
  have hAt : ∀ a : classicalBit,
      (∑ x1 : xOne,
          D.xBoundary2 x1 x2 * xOneBitSlice x a x1) =
        ∑ b' : classicalCheck,
          D.classicalBoundary b' a * xTwoCheckSlice x b' x2 := by
    intro a
    have h := congrFun hxZero (x2, a)
    simp only [Pi.zero_apply] at h
    rw [transpose_boundary2_apply] at h
    have hNeg := eq_neg_of_add_eq_zero_left h
    simpa [ZModModule.neg_eq_self] using hNeg
  change wordLinearMapTranspose (Matrix.toLin' D.xBoundary2)
    (sourceCochainLift S x b) x2 = xTwoCheckSlice x b x2
  rw [wordLinearMapTranspose_toLin'_apply]
  simp only [sourceCochainLift, sourceCochainContraction,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x1 : xOne,
        (∑ a : classicalBit, S a b * xOneBitSlice x a x1) *
          D.xBoundary2 x1 x2) =
        ∑ a : classicalBit, S a b *
          (∑ x1 : xOne,
            D.xBoundary2 x1 x2 * xOneBitSlice x a x1) := by
      simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = ∑ b' : classicalCheck,
        (D.classicalBoundary * S) b' b * xTwoCheckSlice x b' x2 := by
      simp_rw [hAt]
      simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = xTwoCheckSlice x b x2 := by
      change D.classicalBoundary * S = 1 at hS
      rw [hS, Fintype.sum_eq_single b]
      · simp
      · intro b' hne
        rw [Matrix.one_apply]
        simp [hne]

/-- Choose a source degree-zero filling of every projected slice. -/
noncomputable def projectedSourceCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) : Word (ZMod 2) xZero :=
  Classical.choose
    (((sourceChainComplex D).mem_firstCoboundaryCheckCode_iff
      (projectedSourceCochain D S x a)).1 (hFill a))

theorem transpose_sourceBoundary1_projectedSourceCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) :
    wordLinearMapTranspose (sourceChainComplex D).boundary1
      (projectedSourceCochainFilling D S x hFill a) =
        projectedSourceCochain D S x a :=
  Classical.choose_spec
    (((sourceChainComplex D).mem_firstCoboundaryCheckCode_iff
      (projectedSourceCochain D S x a)).1 (hFill a))

/-- Assemble the degree-zero source fillings and right-inverse lifts into one
product degree-zero cochain. -/
noncomputable def productCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck) :=
  Sum.elim
    (fun p => projectedSourceCochainFilling D S x hFill p.2 p.1)
    (fun p => sourceCochainLift S x p.2 p.1)

theorem transpose_boundary1_productCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    wordLinearMapTranspose (boundary1 D)
      (productCochainFilling D S x hFill) = x := by
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x1, a⟩
      rw [transpose_boundary1_apply_inl]
      have hSource := congrFun
        (transpose_sourceBoundary1_projectedSourceCochainFilling
          D S x hFill a) x1
      have hFirst :
          (∑ x0 : xZero,
            D.xBoundary1 x0 x1 *
              productCochainFilling D S x hFill (Sum.inl (x0, a))) =
            projectedSourceCochain D S x a x1 := by
        calc
          (∑ x0 : xZero,
              D.xBoundary1 x0 x1 *
                productCochainFilling D S x hFill (Sum.inl (x0, a))) =
              ∑ x0 : xZero,
                projectedSourceCochainFilling D S x hFill a x0 *
                  D.xBoundary1 x0 x1 := by
            apply Finset.sum_congr rfl
            intro x0 _hx0
            change D.xBoundary1 x0 x1 *
                projectedSourceCochainFilling D S x hFill a x0 =
              projectedSourceCochainFilling D S x hFill a x0 *
                D.xBoundary1 x0 x1
            exact mul_comm _ _
          _ = projectedSourceCochain D S x a x1 := by
            simpa [sourceChainComplex,
              wordLinearMapTranspose_toLin'_apply] using hSource
      rw [hFirst]
      have hProjected := congrFun (projectedSourceCochain_eq D S x a) x1
      rw [hProjected]
      simp only [productCochainFilling, sourceCochainLift,
        Sum.elim_inr, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, xOneBitSlice]
      calc
        (x (Sum.inl (x1, a)) +
            ∑ b : classicalCheck,
              D.classicalBoundary b a *
                sourceCochainContraction x (fun a => S a b) x1) +
            ∑ b : classicalCheck,
              D.classicalBoundary b a *
                sourceCochainContraction x (fun a => S a b) x1 =
          x (Sum.inl (x1, a)) +
            ((∑ b : classicalCheck,
                D.classicalBoundary b a *
                  sourceCochainContraction x (fun a => S a b) x1) +
             (∑ b : classicalCheck,
                D.classicalBoundary b a *
                  sourceCochainContraction x (fun a => S a b) x1)) := by
            ac_rfl
        _ = x (Sum.inl (x1, a)) := by
          rw [ZModModule.add_self, add_zero]
  | inr q =>
      rcases q with ⟨x2, b⟩
      rw [transpose_boundary1_apply_inr]
      have hLift := congrFun
        (transpose_sourceBoundary2_sourceCochainLift D S hS x hx b) x2
      simpa [sourceChainComplex, wordLinearMapTranspose_toLin'_apply,
        productCochainFilling, sourceCochainLift, mul_comm,
        xTwoCheckSlice] using hLift

theorem mem_firstCoboundaryCheckCode_of_projected_slices
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    x ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  apply ((chainComplex D).mem_firstCoboundaryCheckCode_iff x).2
  exact ⟨productCochainFilling D S x hFill,
    transpose_boundary1_productCochainFilling D S hS x hx hFill⟩

/-- EKZ20 Theorem 2.3, cohomological-distance half: the product preserves the
source cohomological distance. -/
theorem middleCohomologyDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by
  intro x hx hNonboundary
  by_contra hNotLower
  have hWeight : HammingWeight x < d := by omega
  have hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier := by
    intro a
    exact projectedSourceCochain_mem_firstCoboundary_of_weight_lt
      D S hS hDistance x hx hWeight a
  exact hNonboundary
    (mem_firstCoboundaryCheckCode_of_projected_slices
      D S hS x hx hFill)

/-- Every `X₁` slice of a product cycle is a cycle in the source complex. -/
theorem xOneBitSlice_mem_middleCycleCode
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    xOneBitSlice z a ∈ (sourceChainComplex D).middleCycleCode.carrier := by
  rw [(sourceChainComplex D).mem_middleCycleCode_iff]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  change boundary1 D z = 0 at hzZero
  ext x0
  have hAt := congrFun hzZero (Sum.inl (x0, a))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inl] at hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, xOneBitSlice] using hAt

/-- A source-cycle slice, packaged in the cycle subspace. -/
noncomputable def sourceCycleSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    (sourceChainComplex D).middleCycleCode.carrier :=
  ⟨xOneBitSlice z a, xOneBitSlice_mem_middleCycleCode D z hz a⟩

/-- The source homology class carried by one classical-bit slice. -/
noncomputable def sourceHomologySlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) : (sourceChainComplex D).middleHomology :=
  (sourceChainComplex D).middleBoundaryInCycles.mkQ
    (sourceCycleSlice D z hz a)

/-- The classical parity-check equations hold with values in source
homology.  This is the Künneth slice relation used for the multiplicative
distance bound. -/
theorem sum_classicalBoundary_smul_sourceHomologySlice_eq_zero
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (b : classicalCheck) :
    (∑ a : classicalBit,
      D.classicalBoundary b a • sourceHomologySlice D z hz a) = 0 := by
  change (∑ a : classicalBit,
      (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (D.classicalBoundary b a • sourceCycleSlice D z hz a)) = 0
  rw [← map_sum]
  apply (Submodule.Quotient.mk_eq_zero
    (sourceChainComplex D).middleBoundaryInCycles).2
  have hCoe :
      (↑(∑ a : classicalBit,
          D.classicalBoundary b a • sourceCycleSlice D z hz a) :
        Word (ZMod 2) xOne) =
        ∑ a : classicalBit,
          D.classicalBoundary b a • xOneBitSlice z a := by
    ext x1
    simp [sourceCycleSlice]
  change (↑(∑ a : classicalBit,
      D.classicalBoundary b a • sourceCycleSlice D z hz a) :
        Word (ZMod 2) xOne) ∈
      (sourceChainComplex D).middleBoundaryCode.carrier
  rw [hCoe]
  apply ((sourceChainComplex D).mem_middleBoundaryCode_iff _).2
  refine ⟨xTwoCheckSlice z b, ?_⟩
  ext x1
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  change boundary1 D z = 0 at hzZero
  have hAt := congrFun hzZero (Sum.inr (x1, b))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inr] at hAt
  have hNeg := eq_neg_of_add_eq_zero_left hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, sourceCycleSlice, xTwoCheckSlice,
    ZModModule.neg_eq_self] using hNeg.symm

theorem sourceHomologySlice_ne_zero_iff
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    sourceHomologySlice D z hz a ≠ 0 ↔
      xOneBitSlice z a ∉
        (sourceChainComplex D).middleBoundaryCode.carrier := by
  constructor
  · intro hClass hBoundary
    apply hClass
    apply (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex D).middleBoundaryInCycles).2
    exact hBoundary
  · intro hBoundary hClass
    apply hBoundary
    exact (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex D).middleBoundaryInCycles).1 hClass

/-- Apply a scalar-valued dual functional to the homology-valued slice word. -/
noncomputable def classicalWordOfHomologyFunctional
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    Word (ZMod 2) classicalBit :=
  fun a => φ (sourceHomologySlice D z hz a)

theorem classicalWordOfHomologyFunctional_mem_kernel
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    Matrix.toLin' D.classicalBoundary
      (classicalWordOfHomologyFunctional D z hz φ) = 0 := by
  ext b
  have hRelation :=
    sum_classicalBoundary_smul_sourceHomologySlice_eq_zero D z hz b
  have hApplied := congrArg φ hRelation
  simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    classicalWordOfHomologyFunctional] using hApplied

/-- Hamming weight is the sum of its nonzero-coordinate indicators. -/
theorem HammingWeight_eq_sum_indicator
    {i : Type u} [Fintype i] (w : Word (ZMod 2) i) :
    HammingWeight w = ∑ j : i, if w j ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]

/-- The first product block decomposes exactly into its disjoint
classical-bit slices. -/
theorem HammingWeight_inlBlock_eq_sum_xOneBitSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    HammingWeight (fun p : xOne × classicalBit => z (Sum.inl p)) =
      ∑ a : classicalBit, HammingWeight (xOneBitSlice z a) := by
  rw [HammingWeight_eq_sum_indicator]
  simp_rw [HammingWeight_eq_sum_indicator]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The sum of the source-slice weights is bounded by the whole product
word; the omitted second block contributes a nonnegative weight. -/
theorem sum_HammingWeight_xOneBitSlice_le
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    (∑ a : classicalBit, HammingWeight (xOneBitSlice z a)) ≤
      HammingWeight z := by
  calc
    (∑ a : classicalBit, HammingWeight (xOneBitSlice z a)) =
        HammingWeight
          (fun p : xOne × classicalBit => z (Sum.inl p)) :=
      (HammingWeight_inlBlock_eq_sum_xOneBitSlice z).symm
    _ ≤ HammingWeight z := by
      rw [HammingWeight_eq_sum_indicator (w := z)]
      rw [Fintype.sum_sum_type]
      rw [HammingWeight_eq_sum_indicator]
      omega

theorem HammingWeight_xOneBitSlice_le
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    HammingWeight (xOneBitSlice z a) ≤ HammingWeight z := by
  classical
  let f : {x1 : xOne // xOneBitSlice z a x1 ≠ 0} →
      {q : QubitIndex xOne xTwo classicalBit classicalCheck // z q ≠ 0} :=
    fun x1 => ⟨Sum.inl (x1.1, a), x1.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun q => q.1) hxy
    have hp := Sum.inl.inj h
    exact congrArg Prod.fst hp
  calc
    HammingWeight (xOneBitSlice z a) =
        Fintype.card {x1 : xOne // xOneBitSlice z a x1 ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ ≤ Fintype.card
        {q : QubitIndex xOne xTwo classicalBit classicalCheck // z q ≠ 0} :=
      Fintype.card_le_of_injective f hf
    _ = HammingWeight z := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Below the source homology distance, every `X₁` slice of a product cycle is
already a source boundary.  The remaining EKZ argument uses surjectivity of the
classical boundary to choose these fillings compatibly. -/
theorem xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hWeight : HammingWeight z < d)
    (a : classicalBit) :
    xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier := by
  by_contra hNonboundary
  have hSliceCycle := xOneBitSlice_mem_middleCycleCode D z hz a
  have hLower := hDistance (xOneBitSlice z a) hSliceCycle hNonboundary
  have hUpper := HammingWeight_xOneBitSlice_le z a
  omega

noncomputable def xTwoBitFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (a : classicalBit) : Word (ZMod 2) xTwo :=
  Classical.choose
    (((sourceChainComplex D).mem_middleBoundaryCode_iff
      (xOneBitSlice z a)).1 (hFill a))

theorem source_boundary2_xTwoBitFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (a : classicalBit) :
    (sourceChainComplex D).boundary2 (xTwoBitFilling D z hFill a) =
      xOneBitSlice z a :=
  Classical.choose_spec
    (((sourceChainComplex D).mem_middleBoundaryCode_iff
      (xOneBitSlice z a)).1 (hFill a))

/-- Assemble the independently chosen source fillings into a product
degree-two word. -/
noncomputable def productSliceFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (C2Index xTwo classicalBit) :=
  fun p => xTwoBitFilling D z hFill p.2 p.1

theorem boundary2_productSliceFilling_apply_inl
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x1 : xOne) (a : classicalBit) :
    boundary2 D (productSliceFilling D z hFill) (Sum.inl (x1, a)) =
      z (Sum.inl (x1, a)) := by
  rw [boundary2_apply_inl]
  have hAt := congrFun (source_boundary2_xTwoBitFilling D z hFill a) x1
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, productSliceFilling, xTwoBitSlice, xOneBitSlice] using hAt

/-- Remove the independently filled `X₁ ⊗ A` block from a product word. -/
noncomputable def sliceRemainder
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  z + boundary2 D (productSliceFilling D z hFill)

theorem sliceRemainder_apply_inl
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x1 : xOne) (a : classicalBit) :
    sliceRemainder D z hFill (Sum.inl (x1, a)) = 0 := by
  rw [sliceRemainder, Pi.add_apply,
    boundary2_productSliceFilling_apply_inl]
  exact ZModModule.add_self _

theorem sliceRemainder_mem_middleCycleCode
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    sliceRemainder D z hFill ∈ (chainComplex D).middleCycleCode.carrier := by
  apply (chainComplex D).middleCycleCode.carrier.add_mem hz
  apply (chainComplex D).middleBoundaryCode_le_middleCycleCode
  exact ((chainComplex D).mem_middleBoundaryCode_iff _).2
    ⟨productSliceFilling D z hFill, rfl⟩

/-- After clearing the first block of a product cycle, each residual `X₂`
slice lies in the degree-two kernel of the source complex. -/
theorem source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (b : classicalCheck) :
    (sourceChainComplex D).boundary2
      (xTwoCheckSlice (sliceRemainder D z hFill) b) = 0 := by
  have hCycle := sliceRemainder_mem_middleCycleCode D z hz hFill
  have hZero := ((chainComplex D).mem_middleCycleCode_iff _).1 hCycle
  change boundary1 D (sliceRemainder D z hFill) = 0 at hZero
  ext x1
  have hAt := congrFun hZero (Sum.inr (x1, b))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inr] at hAt
  have hFirst :
      (∑ a : classicalBit,
        D.classicalBoundary b a *
          xOneBitSlice (sliceRemainder D z hFill) a x1) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    simp [xOneBitSlice, sliceRemainder_apply_inl]
  rw [hFirst, zero_add] at hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, xTwoCheckSlice] using hAt

/-- Lift the residual `X₂ ⊗ B` block through a chosen classical right inverse. -/
noncomputable def residualLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (C2Index xTwo classicalBit) :=
  fun p =>
    ∑ b : classicalCheck,
      S p.2 b * sliceRemainder D z hFill (Sum.inr (p.1, b))

theorem boundary2_residualLift_apply_inr
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x2 : xTwo) (b : classicalCheck) :
    boundary2 D (residualLift D S z hFill) (Sum.inr (x2, b)) =
      sliceRemainder D z hFill (Sum.inr (x2, b)) := by
  rw [boundary2_apply_inr]
  simp only [xTwoBitSlice, residualLift]
  calc
    (∑ a : classicalBit,
        D.classicalBoundary b a *
          ∑ b' : classicalCheck,
            S a b' * sliceRemainder D z hFill (Sum.inr (x2, b'))) =
        ∑ b' : classicalCheck,
          (D.classicalBoundary * S) b b' *
            sliceRemainder D z hFill (Sum.inr (x2, b')) := by
      simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = sliceRemainder D z hFill (Sum.inr (x2, b)) := by
      change D.classicalBoundary * S = 1 at hS
      rw [hS]
      rw [Fintype.sum_eq_single b]
      · simp
      · intro b' hne
        simp [Ne.symm hne]

theorem boundary2_residualLift_apply_inl
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x1 : xOne) (a : classicalBit) :
    boundary2 D (residualLift D S z hFill) (Sum.inl (x1, a)) = 0 := by
  rw [boundary2_apply_inl]
  simp only [xTwoBitSlice, residualLift]
  calc
    (∑ x2 : xTwo,
        D.xBoundary2 x1 x2 *
          ∑ b : classicalCheck,
            S a b * sliceRemainder D z hFill (Sum.inr (x2, b))) =
        ∑ b : classicalCheck,
          S a b *
            (sourceChainComplex D).boundary2
              (xTwoCheckSlice (sliceRemainder D z hFill) b) x1 := by
      simp [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, xTwoCheckSlice, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      rw [congrFun
        (source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
          D z hz hFill b) x1]
      simp

theorem boundary2_residualLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    boundary2 D (residualLift D S z hFill) = sliceRemainder D z hFill := by
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x1, a⟩
      rw [boundary2_residualLift_apply_inl D S z hz hFill x1 a]
      exact (sliceRemainder_apply_inl D z hFill x1 a).symm
  | inr q =>
      rcases q with ⟨x2, b⟩
      exact boundary2_residualLift_apply_inr D S hS z hFill x2 b

theorem mem_middleBoundaryCode_of_slices
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by
  apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
  refine ⟨productSliceFilling D z hFill + residualLift D S z hFill, ?_⟩
  rw [map_add]
  change boundary2 D (productSliceFilling D z hFill) +
    boundary2 D (residualLift D S z hFill) = z
  rw [boundary2_residualLift D S hS z hz hFill]
  ext q
  simp only [sliceRemainder, Pi.add_apply]
  calc
    boundary2 D (productSliceFilling D z hFill) q +
        (z q + boundary2 D (productSliceFilling D z hFill) q) =
      z q +
        (boundary2 D (productSliceFilling D z hFill) q +
          boundary2 D (productSliceFilling D z hFill) q) := by
      ac_rfl
    _ = z q := by rw [ZModModule.add_self, add_zero]

/-- Surjectivity of the classical boundary supplies the right inverse used by
the slice-filling argument.  In particular, callers do not provide an
auxiliary matrix representation or a chosen inverse. -/
theorem exists_classicalRightInverse_of_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary)) :
    ∃ S : Matrix classicalBit classicalCheck (ZMod 2),
      IsClassicalRightInverse D S := by
  let f := Matrix.toLin' D.classicalBoundary
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hSurjective)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  change D.classicalBoundary * LinearMap.toMatrix' g = 1
  rw [← LinearMap.toMatrix'_toLin' D.classicalBoundary]
  rw [← LinearMap.toMatrix'_comp]
  rw [hg]
  exact LinearMap.toMatrix'_id

/-- EKZ20 Theorem 2.3, homological-distance half: a classical right inverse
preserves the source middle-homology distance. -/
theorem middleHomologyDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by
  intro z hz hNonboundary
  by_contra hNotLower
  have hWeight : HammingWeight z < d := by omega
  have hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈
        (sourceChainComplex D).middleBoundaryCode.carrier := by
    intro a
    exact xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
      D hDistance z hz hWeight a
  exact hNonboundary (mem_middleBoundaryCode_of_slices D S hS z hz hFill)

/-- Applying any homology functional gives no more total weighted support than
the disjoint source slices of the product word. -/
theorem mul_HammingWeight_classicalWordOfHomologyFunctional_le
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    d * HammingWeight (classicalWordOfHomologyFunctional D z hz φ) ≤
      HammingWeight z := by
  rw [HammingWeight_eq_sum_indicator, Finset.mul_sum]
  apply (Finset.sum_le_sum fun a _ha => ?_).trans
    (sum_HammingWeight_xOneBitSlice_le z)
  by_cases ha : classicalWordOfHomologyFunctional D z hz φ a ≠ 0
  · rw [if_pos ha, mul_one]
    apply hDistance (xOneBitSlice z a)
      (xOneBitSlice_mem_middleCycleCode D z hz a)
    rw [← sourceHomologySlice_ne_zero_iff D z hz a]
    intro hClass
    apply ha
    change φ (sourceHomologySlice D z hz a) = 0
    rw [hClass]
    exact map_zero φ
  · rw [if_neg ha, mul_zero]
    exact Nat.zero_le (HammingWeight (xOneBitSlice z a))

theorem exists_sourceHomologySlice_ne_zero_of_product_nonboundary
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hNonboundary : z ∉ (chainComplex D).middleBoundaryCode.carrier) :
    ∃ a : classicalBit, sourceHomologySlice D z hz a ≠ 0 := by
  by_contra hNone
  have hAll : ∀ a : classicalBit,
      xOneBitSlice z a ∈
        (sourceChainComplex D).middleBoundaryCode.carrier := by
    intro a
    by_contra ha
    apply hNone
    exact ⟨a, (sourceHomologySlice_ne_zero_iff D z hz a).2 ha⟩
  exact hNonboundary
    (mem_middleBoundaryCode_of_slices D S hS z hz hAll)

theorem exists_homologyFunctional_eq_one
    {x : (sourceChainComplex D).middleHomology}
    (hx : x ≠ 0) :
    ∃ φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology,
      φ x = 1 :=
  Module.Projective.exists_dual_eq_one (ZMod 2) hx

theorem exists_detectingClassicalWord_of_product_nonboundary
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {dSource : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hNonboundary : z ∉ (chainComplex D).middleBoundaryCode.carrier) :
    ∃ w : Word (ZMod 2) classicalBit,
      Matrix.toLin' D.classicalBoundary w = 0 ∧
      w ≠ 0 ∧
      dSource * HammingWeight w ≤ HammingWeight z := by
  obtain ⟨a, hClass⟩ :=
    exists_sourceHomologySlice_ne_zero_of_product_nonboundary
      D S hS z hz hNonboundary
  obtain ⟨φ, hφ⟩ := exists_homologyFunctional_eq_one D hClass
  let w := classicalWordOfHomologyFunctional D z hz φ
  refine ⟨w, classicalWordOfHomologyFunctional_mem_kernel D z hz φ,
    ?_, mul_HammingWeight_classicalWordOfHomologyFunctional_le
      D hSource z hz φ⟩
  intro hw
  have hAt := congrFun hw a
  change φ (sourceHomologySlice D z hz a) = 0 at hAt
  rw [hφ] at hAt
  exact one_ne_zero hAt

theorem distance_product_le_of_detectingClassicalWord
    {dSource dClassical total : Nat}
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical)
    (w : Word (ZMod 2) classicalBit)
    (hwKernel : Matrix.toLin' D.classicalBoundary w = 0)
    (hwNonzero : w ≠ 0)
    (hwBound : dSource * HammingWeight w ≤ total) :
    dClassical * dSource ≤ total := by
  change (∀ v : Word (ZMod 2) classicalBit,
      Matrix.toLin' D.classicalBoundary v = 0 →
      v ≠ 0 → dClassical ≤ HammingWeight v) at hClassical
  have hClassicalWeight : dClassical ≤ HammingWeight w :=
    hClassical w hwKernel hwNonzero
  calc
    dClassical * dSource ≤ HammingWeight w * dSource :=
      Nat.mul_le_mul_right dSource hClassicalWeight
    _ = dSource * HammingWeight w := Nat.mul_comm _ _
    _ ≤ total := hwBound

/-- EKZ20 Theorem 2.3, multiplicative homological-distance bound.  The
homology-valued slice word satisfies the classical parity checks; a dual
functional detects one nonzero slice and turns it into an ordinary nonzero
classical codeword. -/
theorem middleHomologyDistanceAtLeast_mul
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by
  intro z hz hNonboundary
  obtain ⟨w, hwKernel, hwNonzero, hwBound⟩ :=
    exists_detectingClassicalWord_of_product_nonboundary
      D S hS hSource z hz hNonboundary
  exact distance_product_le_of_detectingClassicalWord
    D hClassical w hwKernel hwNonzero hwBound

/-- EKZ20 Theorem 2.3, homological-distance half in its structural form:
surjectivity of the classical boundary is enough to preserve the source
middle-homology distance. -/
theorem middleHomologyDistanceAtLeast_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleHomologyDistanceAtLeast D S hS hDistance

/-- Structural form of the full multiplicative distance theorem: callers
provide only surjectivity and the two genuine distance bounds. -/
theorem middleHomologyDistanceAtLeast_mul_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleHomologyDistanceAtLeast_mul
    D S hS hSource hClassical

/-- Structural cohomological half: surjectivity supplies the internal right
inverse, and the product preserves source cohomological distance. -/
theorem middleCohomologyDistanceAtLeast_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleCohomologyDistanceAtLeast D S hS hDistance

/-- The two finite EKZ20 distance conclusions in one assumption-minimal
interface. -/
theorem distanceBounds_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {dHomology dCohomology dClassical : Nat}
    (hHomology : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) dCohomology)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
        (chainComplex D) (dClassical * dHomology) ∧
      MiddleCohomologyDistanceAtLeast
        (chainComplex D) dCohomology := by
  exact ⟨
    middleHomologyDistanceAtLeast_mul_of_classical_surjective
      D hSurjective hHomology hClassical,
    middleCohomologyDistanceAtLeast_of_classical_surjective
      D hSurjective hCohomology⟩

/-- Exact physical-qubit count of the finite EKZ product. -/
theorem card_qubitIndex :
    Fintype.card (QubitIndex xOne xTwo classicalBit classicalCheck) =
      Fintype.card xOne * Fintype.card classicalBit +
        Fintype.card xTwo * Fintype.card classicalCheck := by
  simp [QubitIndex]

end QEC.Coding.DistanceBalancing
