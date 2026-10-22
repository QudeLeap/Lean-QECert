import QEC.Coding.HypergraphProduct.Dimension.Realization

/-!
# Boundary-map realization for the Tillich--Zémor hypergraph product

The lemmas in this module expand the two concrete block boundary matrices
coordinate by coordinate.  They are the auditable bridge between the matrix
construction and the abstract tensor-kernel theorem.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

open TensorProduct

theorem boundary1Transpose_inl_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C0Index rowOne colTwo)) (c₁ : colOne) (c₂ : colTwo) :
    wordLinearMapTranspose (boundary1 D) x (Sum.inl (c₁, c₂)) =
      ∑ r₁ : rowOne, x (r₁, c₂) * D.first r₁ c₁ := by
  rw [boundary1, wordLinearMapTranspose_toLin'_apply]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply]
  simp

theorem boundary1Transpose_inr_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C0Index rowOne colTwo)) (r₁ : rowOne) (r₂ : rowTwo) :
    wordLinearMapTranspose (boundary1 D) x (Sum.inr (r₁, r₂)) =
      -∑ c₂ : colTwo, x (r₁, c₂) * D.second r₂ c₂ := by
  rw [boundary1, wordLinearMapTranspose_toLin'_apply]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inr_apply]
  simp [mul_neg, Finset.sum_neg_distrib]

theorem boundary2_inl_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C2Index colOne rowTwo)) (c₁ : colOne) (c₂ : colTwo) :
    boundary2 D x (Sum.inl (c₁, c₂)) =
      ∑ r₂ : rowTwo, D.second r₂ c₂ * x (c₁, r₂) := by
  rw [boundary2]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, boundary2Matrix_inl_apply]
  simp

theorem boundary2_inr_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C2Index colOne rowTwo)) (r₁ : rowOne) (r₂ : rowTwo) :
    boundary2 D x (Sum.inr (r₁, r₂)) =
      ∑ c₁ : colOne, D.first r₁ c₁ * x (c₁, r₂) := by
  rw [boundary2]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, boundary2Matrix_inr_apply]
  simp

/-- Apply a pair of one-factor tensor maps and then realize both outputs in
finite product coordinates. -/
def jointTensorWordMap
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B') :
    (Word F A ⊗[F] Word F B) →ₗ[F]
      Word F (A' × B) × Word F (A × B') :=
  ((wordTensorEquiv F A' B).prodCongr
      (wordTensorEquiv F A B')).toLinearMap.comp
    (jointTensorMap f g)

@[simp]
theorem jointTensorWordMap_tmul_fst_apply
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B')
    (x : Word F A) (y : Word F B) (a' : A') (b : B) :
    (jointTensorWordMap f g (x ⊗ₜ[F] y)).1 (a', b) = f x a' * y b := by
  simp [jointTensorWordMap, jointTensorMap]

@[simp]
theorem jointTensorWordMap_tmul_snd_apply
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B')
    (x : Word F A) (y : Word F B) (a : A) (b' : B') :
    (jointTensorWordMap f g (x ⊗ₜ[F] y)).2 (a, b') = x a * g y b' := by
  simp [jointTensorWordMap, jointTensorMap]

/-- The concrete transpose of the first binary boundary, conjugated from its
check-word domain to tensor coordinates and split into its two qubit blocks. -/
def boundary1TransposeTensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (Word (ZMod 2) rowOne ⊗[ZMod 2] Word (ZMod 2) colTwo) →ₗ[ZMod 2]
      Word (ZMod 2) (colOne × colTwo) ×
        Word (ZMod 2) (rowOne × rowTwo) :=
  (wordSumEquiv (ZMod 2) (colOne × colTwo) (rowOne × rowTwo)).toLinearMap.comp
    ((wordLinearMapTranspose (boundary1 D)).comp
      (wordTensorEquiv (ZMod 2) rowOne colTwo).toLinearMap)

/-- The concrete second binary boundary, conjugated from tensor coordinates
and with its physical blocks listed in the tensor-map order. -/
def boundary2TensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (Word (ZMod 2) colOne ⊗[ZMod 2] Word (ZMod 2) rowTwo) →ₗ[ZMod 2]
      Word (ZMod 2) (rowOne × rowTwo) ×
        Word (ZMod 2) (colOne × colTwo) :=
  (wordSumEquivSwap (ZMod 2) (colOne × colTwo)
      (rowOne × rowTwo)).toLinearMap.comp
    ((boundary2 D).comp
      (wordTensorEquiv (ZMod 2) colOne rowTwo).toLinearMap)

theorem boundary1TransposeTensorMap_eq_joint
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    boundary1TransposeTensorMap D =
      jointTensorWordMap (Matrix.toLin' D.first.transpose)
        (Matrix.toLin' D.second) := by
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · funext q
    rcases q with ⟨c₁, c₂⟩
    change wordLinearMapTranspose (boundary1 D)
        (wordTensorEquiv (ZMod 2) rowOne colTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inl (c₁, c₂)) = _
    calc
      _ = ∑ r₁ : rowOne,
          wordTensorEquiv (ZMod 2) rowOne colTwo
              (x ⊗ₜ[ZMod 2] y) (r₁, c₂) * D.first r₁ c₁ :=
        boundary1Transpose_inl_apply D _ c₁ c₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_fst_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r₁ _hr₁
        ring
  · funext q
    rcases q with ⟨r₁, r₂⟩
    change wordLinearMapTranspose (boundary1 D)
        (wordTensorEquiv (ZMod 2) rowOne colTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inr (r₁, r₂)) = _
    calc
      _ = -∑ c₂ : colTwo,
          wordTensorEquiv (ZMod 2) rowOne colTwo
              (x ⊗ₜ[ZMod 2] y) (r₁, c₂) * D.second r₂ c₂ :=
        boundary1Transpose_inr_apply D _ r₁ r₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_snd_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct]
        rw [ZMod.neg_eq_self_mod_two, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c₂ _hc₂
        ring

theorem boundary2TensorMap_eq_joint
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    boundary2TensorMap D =
      jointTensorWordMap (Matrix.toLin' D.first)
        (Matrix.toLin' D.second.transpose) := by
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · funext q
    rcases q with ⟨r₁, r₂⟩
    change boundary2 D
        (wordTensorEquiv (ZMod 2) colOne rowTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inr (r₁, r₂)) = _
    calc
      _ = ∑ c₁ : colOne, D.first r₁ c₁ *
          wordTensorEquiv (ZMod 2) colOne rowTwo
            (x ⊗ₜ[ZMod 2] y) (c₁, r₂) :=
        boundary2_inr_apply D _ r₁ r₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_fst_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c₁ _hc₁
        ring
  · funext q
    rcases q with ⟨c₁, c₂⟩
    change boundary2 D
        (wordTensorEquiv (ZMod 2) colOne rowTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inl (c₁, c₂)) = _
    calc
      _ = ∑ r₂ : rowTwo, D.second r₂ c₂ *
          wordTensorEquiv (ZMod 2) colOne rowTwo
            (x ⊗ₜ[ZMod 2] y) (c₁, r₂) :=
        boundary2_inl_apply D _ c₁ c₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_snd_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r₂ _hr₂
        ring

end QEC.Coding.HypergraphProduct
