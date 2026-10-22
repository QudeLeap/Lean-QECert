import QEC.Coding.HypergraphProduct.Core
import QEC.Coding.CSS.ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Input-code parameters used by the Tillich--Zémor hypergraph product

This file connects each input parity-check matrix to its classical kernel code
and to the kernel code of its transpose.  In particular, the transpose-code
dimensions below are derived from the matrices; they are not supplied as
parameter assumptions.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- The classical code checked by the first input matrix. -/
def firstCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F colOne :=
  parityCheckKernelCode (Matrix.toLin' D.first)

/-- The classical code checked by the second input matrix. -/
def secondCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F colTwo :=
  parityCheckKernelCode (Matrix.toLin' D.second)

/-- The transpose code of the first Tanner graph. -/
def firstTransposeCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F rowOne :=
  parityCheckKernelCode (Matrix.toLin' D.first.transpose)

/-- The transpose code of the second Tanner graph. -/
def secondTransposeCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F rowTwo :=
  parityCheckKernelCode (Matrix.toLin' D.second.transpose)

@[simp]
theorem mem_firstCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F colOne) :
    x ∈ (firstCode D).carrier ↔ Matrix.toLin' D.first x = 0 := by
  exact mem_parityCheckKernelCode _ _

@[simp]
theorem mem_secondCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F colTwo) :
    x ∈ (secondCode D).carrier ↔ Matrix.toLin' D.second x = 0 := by
  exact mem_parityCheckKernelCode _ _

@[simp]
theorem mem_firstTransposeCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F rowOne) :
    x ∈ (firstTransposeCode D).carrier ↔
      Matrix.toLin' D.first.transpose x = 0 := by
  exact mem_parityCheckKernelCode _ _

@[simp]
theorem mem_secondTransposeCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F rowTwo) :
    x ∈ (secondTransposeCode D).carrier ↔
      Matrix.toLin' D.second.transpose x = 0 := by
  exact mem_parityCheckKernelCode _ _

/-- Rank-nullity for a parity-check matrix, stated as code dimension plus
matrix rank equals the number of columns. -/
theorem dimension_kernelCode_add_rank
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (H : Matrix row col F) :
    Dimension (parityCheckKernelCode (Matrix.toLin' H)) + H.rank =
      Fintype.card col := by
  have h := (Matrix.toLin' H).finrank_range_add_finrank_ker
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank F (LinearMap.ker (Matrix.toLin' H)) + H.rank = _
  rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_toLin']
  rw [add_comm]
  simpa using h

/-- The source relation `k₁ + r₁ = n₁ + k₁ᵀ`, avoiding truncated
subtraction. -/
theorem first_dimension_add_rows_eq_cols_add_transpose_dimension
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Dimension (firstCode D) + Fintype.card rowOne =
      Fintype.card colOne + Dimension (firstTransposeCode D) := by
  have hFirst := dimension_kernelCode_add_rank D.first
  have hTranspose := dimension_kernelCode_add_rank D.first.transpose
  rw [Matrix.rank_transpose] at hTranspose
  change
    Dimension (parityCheckKernelCode (Matrix.toLin' D.first)) +
        Fintype.card rowOne =
      Fintype.card colOne +
        Dimension (parityCheckKernelCode (Matrix.toLin' D.first.transpose))
  omega

/-- The source relation `k₂ + r₂ = n₂ + k₂ᵀ`, avoiding truncated
subtraction. -/
theorem second_dimension_add_rows_eq_cols_add_transpose_dimension
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Dimension (secondCode D) + Fintype.card rowTwo =
      Fintype.card colTwo + Dimension (secondTransposeCode D) := by
  have hSecond := dimension_kernelCode_add_rank D.second
  have hTranspose := dimension_kernelCode_add_rank D.second.transpose
  rw [Matrix.rank_transpose] at hTranspose
  change
    Dimension (parityCheckKernelCode (Matrix.toLin' D.second)) +
        Fintype.card rowTwo =
      Fintype.card colTwo +
        Dimension (parityCheckKernelCode (Matrix.toLin' D.second.transpose))
  omega

end QEC.Coding.HypergraphProduct
