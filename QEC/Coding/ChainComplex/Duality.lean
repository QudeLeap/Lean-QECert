import QEC.Coding.ChainComplex.HomotopyDistance

/-!
# Finite-coordinate duals of three-term chain complexes

The dual complex reverses degrees and transposes both boundary maps.  This
module records the exact identification of its middle homology with the
original middle cohomology, including Hamming-distance predicates.
-/

namespace QEC.Coding

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

/-- Transposing a finite-coordinate linear map twice gives the original map. -/
theorem wordLinearMapTranspose_transpose
    (f : Word F i0 →ₗ[F] Word F i1) :
    wordLinearMapTranspose (wordLinearMapTranspose f) = f := by
  apply LinearMap.ext
  intro x
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F)).right
  intro y
  have hPair :
      wordPairing (F := F) y
          (wordLinearMapTranspose (wordLinearMapTranspose f) x) =
        wordPairing (F := F) y (f x) := by
    calc
      wordPairing (F := F) y
          (wordLinearMapTranspose (wordLinearMapTranspose f) x) =
          wordPairing (F := F)
            (wordLinearMapTranspose (wordLinearMapTranspose f) x) y := by
        simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing (F := F) x
            (wordLinearMapTranspose f y) :=
        wordPairing_wordLinearMapTranspose
          (wordLinearMapTranspose f) x y
      _ = wordPairing (F := F)
            (wordLinearMapTranspose f y) x := by
        simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing (F := F) y (f x) :=
        wordPairing_wordLinearMapTranspose f y x
  simpa [wordPairing_apply, dotProduct_sub] using
    sub_eq_zero.mpr hPair

theorem wordLinearMapTranspose_zero :
    wordLinearMapTranspose
      (0 : Word F i0 →ₗ[F] Word F i1) = 0 := by
  classical
  apply LinearMap.ext
  intro x
  ext i
  simp [wordLinearMapTranspose]

/-- Coordinate formula for transposing a matrix-defined word map. -/
theorem wordLinearMapTranspose_toLin'_apply
    {row col : Type v} [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) (x : Word F row) (c : col) :
    wordLinearMapTranspose (Matrix.toLin' M) x c =
      ∑ r : row, x r * M r c := by
  classical
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _hc' hne
    simp [hne]
  · simp

/-- Reverse a three-term finite-coordinate complex and transpose its
boundaries. -/
noncomputable def dualChainComplex
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    ChainComplexData F (Word F i2) (Word F i1) (Word F i0) where
  boundary1 := wordLinearMapTranspose K.boundary2
  boundary2 := wordLinearMapTranspose K.boundary1
  boundary_squared := by
    rw [← wordLinearMapTranspose_comp]
    rw [K.boundary_squared]
    exact wordLinearMapTranspose_zero

@[simp]
theorem dualChainComplex_boundary1
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).boundary1 =
      wordLinearMapTranspose K.boundary2 := rfl

@[simp]
theorem dualChainComplex_boundary2
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).boundary2 =
      wordLinearMapTranspose K.boundary1 := rfl

theorem dual_middleCycleCode_carrier_eq_middleCocycleCode
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).middleCycleCode.carrier =
      K.middleCocycleCode.carrier := rfl

theorem dual_middleBoundaryCode_carrier_eq_firstCoboundaryCheckCode
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).middleBoundaryCode.carrier =
      K.firstCoboundaryCheckCode.carrier := rfl

/-- Middle homology of the finite-coordinate dual is definitionally the
middle cohomology of the original complex, hence their dimensions agree. -/
theorem finrank_middleHomology_dual_eq_middleCohomology
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    Module.finrank F (dualChainComplex K).middleHomology =
      Module.finrank F K.middleCohomology := by
  rfl

/-- Homological distance of the dual is exactly cohomological distance of the
original complex. -/
theorem middleHomologyDistanceAtLeast_dual_iff
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) :
    MiddleHomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleCohomologyDistanceAtLeast K d := by
  rfl

/-- Dualization is involutive at the level of boundary maps. -/
theorem dualChainComplex_dual
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    dualChainComplex (dualChainComplex K) = K := by
  cases K with
  | mk boundary1 boundary2 boundary_squared =>
      simp [dualChainComplex, wordLinearMapTranspose_transpose]

/-- Cohomological distance of the dual is homological distance of the
original complex. -/
theorem middleCohomologyDistanceAtLeast_dual_iff
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) :
    MiddleCohomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleHomologyDistanceAtLeast K d := by
  rw [← middleHomologyDistanceAtLeast_dual_iff
    (dualChainComplex K) d]
  rw [dualChainComplex_dual]

end QEC.Coding
