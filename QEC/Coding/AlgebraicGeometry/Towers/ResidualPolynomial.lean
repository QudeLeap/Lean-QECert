import QEC.Coding.AlgebraicGeometry.Towers.AuxiliaryMinpoly

/-!
# The split residual polynomial in one Garcia--Stichtenoth step

The auxiliary Artin--Schreier polynomial over `F256` has exactly the sixteen
roots already constructed by `f256ArtinSchreierRoots`.  Its literal linear
factorization then classifies its roots after every field extension.  The
proof is symbolic and does not enumerate the 256 field elements.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The roots of the residual auxiliary polynomial are exactly the concrete
sixteen-element Artin--Schreier fibre. -/
theorem stepAuxiliaryPolynomial_roots (a : F256) :
    (stepAuxiliaryPolynomial a).roots =
      (f256ArtinSchreierRoots a : Finset F256).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro b hb
    rw [mem_f256ArtinSchreierRoots] at hb
    simp only [stepAuxiliaryPolynomial, eval_add, eval_pow, eval_X, eval_sub,
      eval_C]
    linear_combination hb
  · rw [stepAuxiliaryPolynomial_natDegree, f256ArtinSchreierRoots_card]
  · exact (stepAuxiliaryPolynomial_monic a).ne_zero

/-- The residual auxiliary polynomial splits completely over `F256`. -/
theorem stepAuxiliaryPolynomial_splits (a : F256) :
    (stepAuxiliaryPolynomial a).Splits := by
  rw [Polynomial.splits_iff_card_roots, stepAuxiliaryPolynomial_roots,
    Finset.card_val, f256ArtinSchreierRoots_card,
    stepAuxiliaryPolynomial_natDegree]

/-- Literal factorization of the residual auxiliary polynomial by its sixteen
distinct roots. -/
theorem stepAuxiliaryPolynomial_eq_prod_roots (a : F256) :
    stepAuxiliaryPolynomial a =
      ∏ b ∈ f256ArtinSchreierRoots a, (X - C b) := by
  rw [(stepAuxiliaryPolynomial_splits a).eq_prod_roots_of_monic
    (stepAuxiliaryPolynomial_monic a), stepAuxiliaryPolynomial_roots]
  simp

/-- Every root after scalar extension is the image of one of the sixteen
concrete residual roots. -/
theorem exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
    {E : Type*} [Field E] [Algebra F256 E] (a : F256) (y : E)
    (hy : Polynomial.aeval y (stepAuxiliaryPolynomial a) = 0) :
    ∃ b ∈ f256ArtinSchreierRoots a,
      y = algebraMap F256 E b := by
  rw [stepAuxiliaryPolynomial_eq_prod_roots] at hy
  simp only [map_prod, aeval_sub, aeval_X, aeval_C,
    Finset.prod_eq_zero_iff] at hy
  obtain ⟨b, hb, hroot⟩ := hy
  exact ⟨b, hb, sub_eq_zero.mp hroot⟩

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
