import QEC.Coding.AlgebraicGeometry.Towers.GaloisBase
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisStep

/-!
# Constant-field splitting for the source Garcia--Stichtenoth recursion

For a finite seed value satisfying `(a^16 + a)^15 = 1`, the right-hand side
of the literal source recursion belongs to the relative constant field
`F16`.  Hence its Artin--Schreier equation has exactly sixteen roots in
`F256`.  This file constructs that fibre and proves the corresponding
residual polynomial factorization symbolically; it does not enumerate the
256 field elements or construct any place, divisor, or tower parameter.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private theorem sourceAlgebraMap_trace_eq_f256ArtinSchreier (x : F256) :
    algebraMap F16 F256 (Algebra.trace F16 F256 x) =
      f256ArtinSchreier x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [f256_finrank_over_f16, Nat.card_eq_fintype_card, f16_card]
  norm_num [Finset.sum_range_succ, f256ArtinSchreier_apply, add_comm]

private theorem sourceSplitPoint_ne_zero (a : GaloisBaseSplitPoint) :
    (a : F256) ≠ 0 := by
  intro hzero
  apply a.property
  rw [galoisBaseWValue_eq, hzero]
  norm_num

private theorem sourceSplitPoint_denominator_ne_zero
    (a : GaloisBaseSplitPoint) :
    (a : F256) ^ 15 + 1 ≠ 0 := by
  intro hzero
  apply a.property
  rw [galoisBaseWValue_eq]
  calc
    (a : F256) ^ 16 + a = a * (a ^ 15 + 1) := by ring
    _ = 0 := by rw [hzero, mul_zero]

private noncomputable def sourceSplitScalar
    (a : GaloisBaseSplitPoint) : F16 :=
  Algebra.norm F16 (a : F256) / Algebra.trace F16 F256 (a : F256)

private theorem algebraMap_sourceSplitScalar
    (a : GaloisBaseSplitPoint) :
    algebraMap F16 F256 (sourceSplitScalar a) =
      sourceStepRhs (a : F256) := by
  have hnorm : algebraMap F16 F256 (Algebra.norm F16 (a : F256)) =
      (a : F256) ^ 17 := by
    rw [FiniteField.algebraMap_norm_eq_pow]
    norm_num [Nat.card_eq_fintype_card, f16_card, f256_card]
  have htrace := sourceAlgebraMap_trace_eq_f256ArtinSchreier (a : F256)
  have hw : (a : F256) ^ 16 + a ≠ 0 := by
    simpa only [galoisBaseWValue_eq] using a.property
  have hden := sourceSplitPoint_denominator_ne_zero a
  rw [sourceSplitScalar, map_div₀, hnorm, htrace,
    f256ArtinSchreier_apply, sourceStepRhs]
  field_simp [hw, hden]

/-- The source recursion right-hand side at a selected finite base point is
fixed by the sixteenth-power Frobenius. -/
theorem sourceStepRhs_fixedByFrobenius (a : GaloisBaseSplitPoint) :
    sourceStepRhs (a : F256) ^ 16 = sourceStepRhs (a : F256) := by
  rw [← algebraMap_sourceSplitScalar]
  rw [← map_pow]
  have hpow := FiniteField.pow_card (sourceSplitScalar a)
  simpa only [f16_card] using congrArg (algebraMap F16 F256) hpow

/-- One actual `F256` solution of the selected source-step Artin--Schreier
equation. -/
noncomputable def sourceStepArtinSchreierRoot
    (a : GaloisBaseSplitPoint) : F256 :=
  Classical.choose
    (Algebra.trace_surjective F16 F256 (sourceSplitScalar a))

private theorem sourceStepArtinSchreierRoot_trace
    (a : GaloisBaseSplitPoint) :
    Algebra.trace F16 F256 (sourceStepArtinSchreierRoot a) =
      sourceSplitScalar a :=
  Classical.choose_spec
    (Algebra.trace_surjective F16 F256 (sourceSplitScalar a))

/-- The chosen constant solves the literal source recursion equation. -/
theorem sourceStepArtinSchreierRoot_spec (a : GaloisBaseSplitPoint) :
    f256ArtinSchreier (sourceStepArtinSchreierRoot a) =
      sourceStepRhs (a : F256) := by
  calc
    f256ArtinSchreier (sourceStepArtinSchreierRoot a) =
        algebraMap F16 F256
          (Algebra.trace F16 F256 (sourceStepArtinSchreierRoot a)) :=
      (sourceAlgebraMap_trace_eq_f256ArtinSchreier _).symm
    _ = algebraMap F16 F256 (sourceSplitScalar a) := by
      rw [sourceStepArtinSchreierRoot_trace]
    _ = sourceStepRhs (a : F256) := algebraMap_sourceSplitScalar a

/-- The literal sixteen-element constant fibre for a selected source step. -/
noncomputable def sourceStepArtinSchreierRoots
    (a : GaloisBaseSplitPoint) : Finset F256 :=
  Finset.univ.filter fun y =>
    f256ArtinSchreier y = sourceStepRhs (a : F256)

theorem mem_sourceStepArtinSchreierRoots
    (a : GaloisBaseSplitPoint) (y : F256) :
    y ∈ sourceStepArtinSchreierRoots a ↔
      y ^ 16 + y = sourceStepRhs (a : F256) := by
  simp [sourceStepArtinSchreierRoots, f256ArtinSchreier_apply]

private noncomputable def sourceStepArtinSchreierKernelEquivRoots
    (a : GaloisBaseSplitPoint) :
    LinearMap.ker f256ArtinSchreier ≃
      ↥(sourceStepArtinSchreierRoots a) where
  toFun y := ⟨sourceStepArtinSchreierRoot a + y, by
    simp only [sourceStepArtinSchreierRoots, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [map_add, sourceStepArtinSchreierRoot_spec, y.property, add_zero]⟩
  invFun y := ⟨y - sourceStepArtinSchreierRoot a, by
    change f256ArtinSchreier (y - sourceStepArtinSchreierRoot a) = 0
    rw [map_sub, sourceStepArtinSchreierRoot_spec]
    have hy : f256ArtinSchreier (y : F256) =
        sourceStepRhs (a : F256) := by
      simpa only [sourceStepArtinSchreierRoots, Finset.mem_filter,
        Finset.mem_univ, true_and] using y.property
    rw [hy, sub_self]⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Every selected source-step Artin--Schreier fibre has exactly sixteen
constant roots. -/
theorem sourceStepArtinSchreierRoots_card (a : GaloisBaseSplitPoint) :
    (sourceStepArtinSchreierRoots a).card = 16 := by
  calc
    (sourceStepArtinSchreierRoots a).card =
        Fintype.card ↥(sourceStepArtinSchreierRoots a) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (LinearMap.ker f256ArtinSchreier) :=
      Fintype.card_congr (sourceStepArtinSchreierKernelEquivRoots a).symm
    _ = 16 := f256ArtinSchreier_ker_card

/-- The residual polynomial of a selected literal source recursion step. -/
noncomputable def sourceStepResidualPolynomial
    (a : GaloisBaseSplitPoint) : F256[X] :=
  X ^ 16 + (X - C (sourceStepRhs (a : F256)))

theorem sourceStepResidualPolynomial_monic (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).Monic := by
  rw [sourceStepResidualPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : F256[X]) - C (sourceStepRhs (a : F256))).degree ≤
        max (X : F256[X]).degree
          (C (sourceStepRhs (a : F256))).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) :=
      max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : F256[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num

@[simp]
theorem sourceStepResidualPolynomial_natDegree (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [sourceStepResidualPolynomial, degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := F256) 16
  · calc
      ((X : F256[X]) - C (sourceStepRhs (a : F256))).degree ≤
          max (X : F256[X]).degree
            (C (sourceStepRhs (a : F256))).degree :=
        degree_sub_le _ _
      _ ≤ (1 : WithBot ℕ) :=
        max_le (by simp) (degree_C_le.trans (by norm_num))
      _ < ((X : F256[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num

/-- The residual polynomial roots are precisely the constructed constant
fibre. -/
theorem sourceStepResidualPolynomial_roots (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).roots =
      (sourceStepArtinSchreierRoots a : Finset F256).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro b hb
    rw [mem_sourceStepArtinSchreierRoots] at hb
    simp only [sourceStepResidualPolynomial, eval_add, eval_pow, eval_X,
      eval_sub, eval_C]
    linear_combination hb
  · rw [sourceStepResidualPolynomial_natDegree,
      sourceStepArtinSchreierRoots_card]
  · exact (sourceStepResidualPolynomial_monic a).ne_zero

/-- The selected source-step residual polynomial splits over `F256`. -/
theorem sourceStepResidualPolynomial_splits (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).Splits := by
  rw [Polynomial.splits_iff_card_roots,
    sourceStepResidualPolynomial_roots, Finset.card_val,
    sourceStepArtinSchreierRoots_card,
    sourceStepResidualPolynomial_natDegree]

/-- Literal factorization into the sixteen distinct constant roots. -/
theorem sourceStepResidualPolynomial_eq_prod_roots
    (a : GaloisBaseSplitPoint) :
    sourceStepResidualPolynomial a =
      ∏ b ∈ sourceStepArtinSchreierRoots a, (X - C b) := by
  rw [(sourceStepResidualPolynomial_splits a).eq_prod_roots_of_monic
    (sourceStepResidualPolynomial_monic a),
    sourceStepResidualPolynomial_roots]
  simp

/-- Every root after scalar extension is the image of one of the sixteen
constructed constants. -/
theorem exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
    {E : Type*} [Field E] [Algebra F256 E]
    (a : GaloisBaseSplitPoint) (y : E)
    (hy : Polynomial.aeval y (sourceStepResidualPolynomial a) = 0) :
    ∃ b ∈ sourceStepArtinSchreierRoots a,
      y = algebraMap F256 E b := by
  rw [sourceStepResidualPolynomial_eq_prod_roots] at hy
  simp only [map_prod, aeval_sub, aeval_X, aeval_C,
    Finset.prod_eq_zero_iff] at hy
  obtain ⟨b, hb, hroot⟩ := hy
  exact ⟨b, hb, sub_eq_zero.mp hroot⟩

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
