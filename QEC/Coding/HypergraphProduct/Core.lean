import QEC.Coding.QLDPC.SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Tillich--Zémor hypergraph-product chain complex

This module defines the general two-input hypergraph product from the two
binary parity-check matrices of Tillich and Zémor.  It contains only the
construction and its independently proved chain-complex and CSS laws; the
dimension and distance theorems are proved in focused downstream modules.

Source: `tillich-zemor-2009-hypergraph-product/ITv5.tex`, especially the
graph-product definition at lines 505--534 and CSS-validity proposition at
lines 639--650.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- The two parity-check matrices defining a general hypergraph product. -/
structure Data (F rowOne colOne rowTwo colTwo : Type*) where
  first : Matrix rowOne colOne F
  second : Matrix rowTwo colTwo F

/-- Degree-zero coordinates, equivalently the X-check coordinates. -/
abbrev C0Index (rowOne colTwo : Type*) := rowOne × colTwo

/-- The two physical-qubit blocks of the hypergraph product. -/
abbrev QubitIndex (rowOne colOne rowTwo colTwo : Type*) :=
  Sum (colOne × colTwo) (rowOne × rowTwo)

/-- Degree-two coordinates, equivalently the Z-check coordinates. -/
abbrev C2Index (colOne rowTwo : Type*) := colOne × rowTwo

/-- Exact blocklength of the two hypergraph-product qubit blocks. -/
theorem card_qubitIndex
    {rowOne colOne rowTwo colTwo : Type*}
    [Fintype rowOne] [Fintype colOne] [Fintype rowTwo] [Fintype colTwo] :
    Fintype.card (QubitIndex rowOne colOne rowTwo colTwo) =
      Fintype.card colOne * Fintype.card colTwo +
        Fintype.card rowOne * Fintype.card rowTwo := by
  simp [QubitIndex]

/-! ## Boundary matrices -/

/--
The first boundary `[H₁ ⊗ I, -I ⊗ H₂ᵀ]`.  Rows are indexed by
`rowOne × colTwo` and columns by the two qubit blocks.
-/
def boundary1Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Matrix (C0Index rowOne colTwo)
      (QubitIndex rowOne colOne rowTwo colTwo) F :=
  fun (r₁, c₂) q =>
    match q with
    | Sum.inl (c₁, c₂') => if c₂ = c₂' then D.first r₁ c₁ else 0
    | Sum.inr (r₁', r₂) => if r₁ = r₁' then -D.second r₂ c₂ else 0

/--
The second boundary `[I ⊗ H₂ᵀ; H₁ ⊗ I]`.  Columns are indexed by
`colOne × rowTwo` and rows by the two qubit blocks.
-/
def boundary2Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Matrix (QubitIndex rowOne colOne rowTwo colTwo)
      (C2Index colOne rowTwo) F :=
  fun q (c₁', r₂') =>
    match q with
    | Sum.inl (c₁, c₂) => if c₁ = c₁' then D.second r₂' c₂ else 0
    | Sum.inr (r₁, r₂) => if r₂ = r₂' then D.first r₁ c₁' else 0

@[simp]
theorem boundary1Matrix_inl_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₂ c₂' : colTwo) (c₁ : colOne) :
    boundary1Matrix D (r₁, c₂) (Sum.inl (c₁, c₂')) =
      if c₂ = c₂' then D.first r₁ c₁ else 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inr_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ r₁' : rowOne) (r₂ : rowTwo) (c₂ : colTwo) :
    boundary1Matrix D (r₁, c₂) (Sum.inr (r₁', r₂)) =
      if r₁ = r₁' then -D.second r₂ c₂ else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inl_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ c₁' : colOne) (r₂ : rowTwo) (c₂ : colTwo) :
    boundary2Matrix D (Sum.inl (c₁, c₂)) (c₁', r₂) =
      if c₁ = c₁' then D.second r₂ c₂ else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inr_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₁ : colOne) (r₂ r₂' : rowTwo) :
    boundary2Matrix D (Sum.inr (r₁, r₂)) (c₁, r₂') =
      if r₂ = r₂' then D.first r₁ c₁ else 0 := by
  rfl

/-- The two hypergraph-product boundary matrices multiply to zero. -/
theorem boundary1Matrix_mul_boundary2Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨r₁, c₂⟩ ⟨c₁, r₂⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  calc
    _ = D.first r₁ c₁ * D.second r₂ c₂ -
        D.second r₂ c₂ * D.first r₁ c₁ := by
      simp [sub_eq_add_neg]
    _ = 0 := by
      rw [mul_comm]
      exact sub_self _

/-! ## Chain complex and induced CSS code -/

/-- The first hypergraph-product boundary as a linear map. -/
noncomputable def boundary1
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo) →ₗ[F]
      Word F (C0Index rowOne colTwo) :=
  Matrix.toLin' (boundary1Matrix D)

/-- The second hypergraph-product boundary as a linear map. -/
noncomputable def boundary2
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Word F (C2Index colOne rowTwo) →ₗ[F]
      Word F (QubitIndex rowOne colOne rowTwo colTwo) :=
  Matrix.toLin' (boundary2Matrix D)

/-- The two boundary maps compose to zero. -/
theorem boundary_squared
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul, boundary1Matrix_mul_boundary2Matrix]
  simp

/-- The honest three-term chain complex of a general hypergraph product. -/
noncomputable def chainComplex
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    ChainComplexData F
      (Word F (C0Index rowOne colTwo))
      (Word F (QubitIndex rowOne colOne rowTwo colTwo))
      (Word F (C2Index colOne rowTwo)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D

@[simp]
theorem chainComplex_boundary1
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (chainComplex D).boundary1 = boundary1 D := by
  rfl

@[simp]
theorem chainComplex_boundary2
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (chainComplex D).boundary2 = boundary2 D := by
  rfl

/-- The binary CSS code induced by the hypergraph-product chain complex. -/
noncomputable def binaryCSSCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    CSSCode (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)
      (Semantics.Qubit.QubitRegister
        (QubitIndex rowOne colOne rowTwo colTwo)) :=
  (chainComplex D).binaryCSSCode

@[simp]
theorem binaryCSSCode_xCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by
  rfl

@[simp]
theorem binaryCSSCode_zCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl

/-- The induced stabilizer satisfies the repository source-validity contract. -/
theorem binaryCSSCode_stabilizer_isSourceValidBinary
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary

end QEC.Coding.HypergraphProduct
