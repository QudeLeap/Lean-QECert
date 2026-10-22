import QEC.Coding.HypergraphProduct.Dimension.BoundaryMaps

/-!
# Exact encoded dimension of the Tillich--Zémor hypergraph product

This module transports the two tensor-kernel calculations back through the
coordinate equivalences and then performs the finite-dimensional Euler
calculation for the concrete three-term chain complex.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- Precomposition by a linear equivalence identifies the two kernels. -/
def kerCompLinearEquiv
    {F : Type v} {V W X : Type u}
    [Semiring F]
    [AddCommMonoid V] [Module F V]
    [AddCommMonoid W] [Module F W]
    [AddCommMonoid X] [Module F X]
    (e : V ≃ₗ[F] W) (f : W →ₗ[F] X) :
    LinearMap.ker (f.comp e.toLinearMap) ≃ₗ[F] LinearMap.ker f where
  toFun x := ⟨e x.1, by
    change f (e x.1) = 0
    exact x.2⟩
  invFun y := ⟨e.symm y.1, by
    change f (e (e.symm y.1)) = 0
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact e.map_smul a x.1

theorem ker_jointTensorWordMap_eq
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B') :
    LinearMap.ker (jointTensorWordMap f g) =
      LinearMap.ker (jointTensorMap f g) := by
  unfold jointTensorWordMap
  exact LinearEquiv.ker_comp _ _

theorem finrank_ker_boundary1TransposeTensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary1TransposeTensorMap D)) =
      Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) := by
  unfold boundary1TransposeTensorMap
  rw [LinearEquiv.ker_comp]
  exact LinearEquiv.finrank_eq
    (kerCompLinearEquiv
      (wordTensorEquiv (ZMod 2) rowOne colTwo)
      (wordLinearMapTranspose (boundary1 D)))

theorem finrank_ker_boundary2TensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary2TensorMap D)) =
      Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) := by
  unfold boundary2TensorMap
  rw [LinearEquiv.ker_comp]
  exact LinearEquiv.finrank_eq
    (kerCompLinearEquiv
      (wordTensorEquiv (ZMod 2) colOne rowTwo) (boundary2 D))

/-- The first endpoint kernel is the product of the first transpose-code
dimension and the second primal-code dimension. -/
theorem finrank_ker_boundary1Transpose_eq
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) =
      Dimension (firstTransposeCode D) * Dimension (secondCode D) := by
  calc
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (boundary1TransposeTensorMap D)) :=
      (finrank_ker_boundary1TransposeTensorMap D).symm
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorWordMap (Matrix.toLin' D.first.transpose)
              (Matrix.toLin' D.second))) := by
      rw [boundary1TransposeTensorMap_eq_joint]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorMap (Matrix.toLin' D.first.transpose)
              (Matrix.toLin' D.second))) := by
      rw [ker_jointTensorWordMap_eq]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.first.transpose)) *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.second)) :=
      finrank_ker_jointTensorMap _ _
    _ = Dimension (firstTransposeCode D) * Dimension (secondCode D) := by
      rfl

/-- The second endpoint kernel is the product of the first primal-code
dimension and the second transpose-code dimension. -/
theorem finrank_ker_boundary2_eq
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) =
      Dimension (firstCode D) * Dimension (secondTransposeCode D) := by
  calc
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (boundary2TensorMap D)) :=
      (finrank_ker_boundary2TensorMap D).symm
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorWordMap (Matrix.toLin' D.first)
              (Matrix.toLin' D.second.transpose))) := by
      rw [boundary2TensorMap_eq_joint]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorMap (Matrix.toLin' D.first)
              (Matrix.toLin' D.second.transpose))) := by
      rw [ker_jointTensorWordMap_eq]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.first)) *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.second.transpose)) :=
      finrank_ker_jointTensorMap _ _
    _ = Dimension (firstCode D) * Dimension (secondTransposeCode D) := by
      rfl

/-- The project transpose of a matrix-defined word map is the word map of the
transposed matrix. -/
theorem wordLinearMapTranspose_toLin'_eq
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    wordLinearMapTranspose (Matrix.toLin' M) = Matrix.toLin' M.transpose := by
  apply LinearMap.ext
  intro x
  funext c
  rw [wordLinearMapTranspose_toLin'_apply]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, mul_comm]

/-- Matrix rank is the finrank of the range of its coordinate word map. -/
theorem finrank_range_toLin'_eq_rank
    {F : Type v} {row col : Type u}
    [Field F]
    [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' M)) = M.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_toLin']

/-- Transposing a finite matrix-defined word map preserves its rank. -/
theorem finrank_range_wordLinearMapTranspose_toLin'_eq
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F
        (LinearMap.range (wordLinearMapTranspose (Matrix.toLin' M))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [wordLinearMapTranspose_toLin'_eq,
    finrank_range_toLin'_eq_rank, finrank_range_toLin'_eq_rank,
    Matrix.rank_transpose]

/-- Exact Künneth dimension formula for the general two-input binary
Tillich--Zémor hypergraph product.  No input matrix is assumed full rank. -/
theorem finrank_middleHomology_eq_dimension_products
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) := by
  have hHomRaw := Submodule.finrank_quotient_add_finrank
    (chainComplex D).middleBoundaryInCycles
  rw [(chainComplex D).finrank_middleBoundaryInCycles_eq] at hHomRaw
  have hHom :
      Module.finrank (ZMod 2) (chainComplex D).middleHomology +
          Module.finrank (ZMod 2) (LinearMap.range (boundary2 D)) =
        Module.finrank (ZMod 2) (LinearMap.ker (boundary1 D)) := by
    exact hHomRaw
  have hBoundary1 := (boundary1 D).finrank_range_add_finrank_ker
  have hBoundary1Transpose :=
    (wordLinearMapTranspose (boundary1 D)).finrank_range_add_finrank_ker
  have hBoundary2 := (boundary2 D).finrank_range_add_finrank_ker
  have hBoundary1Size :
      Module.finrank (ZMod 2) (LinearMap.range (boundary1 D)) +
          Module.finrank (ZMod 2) (LinearMap.ker (boundary1 D)) =
        Fintype.card colOne * Fintype.card colTwo +
          Fintype.card rowOne * Fintype.card rowTwo := by
    simpa [Length, QubitIndex] using hBoundary1
  have hBoundary1TransposeSize :
      Module.finrank (ZMod 2)
          (LinearMap.range (wordLinearMapTranspose (boundary1 D))) +
        Module.finrank (ZMod 2)
          (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) =
        Fintype.card rowOne * Fintype.card colTwo := by
    simpa [Length, C0Index] using hBoundary1Transpose
  have hBoundary2Size :
      Module.finrank (ZMod 2) (LinearMap.range (boundary2 D)) +
          Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) =
        Fintype.card colOne * Fintype.card rowTwo := by
    simpa [Length, C2Index] using hBoundary2
  have hBoundary1Rank :
      Module.finrank (ZMod 2)
          (LinearMap.range (wordLinearMapTranspose (boundary1 D))) =
        Module.finrank (ZMod 2) (LinearMap.range (boundary1 D)) := by
    exact finrank_range_wordLinearMapTranspose_toLin'_eq (boundary1Matrix D)
  have hEndpointOne := finrank_ker_boundary1Transpose_eq D
  have hEndpointTwo := finrank_ker_boundary2_eq D
  have hFirstRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension D
  have hSecondRelation :=
    second_dimension_add_rows_eq_cols_add_transpose_dimension D
  nlinarith

end QEC.Coding.HypergraphProduct
