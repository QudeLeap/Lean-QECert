import QEC.Coding.AlgebraicGeometry.Towers.Galois

import Mathlib.FieldTheory.PrimitiveElement

/-!
# The auxiliary-coordinate minimal polynomial in one GS step

This file proves that the literal Artin--Schreier auxiliary coordinate
generates the already-constructed degree-sixteen step field and identifies
its minimal polynomial.  These facts will be used to construct the actual
split rational places; no place count, divisor, genus, or asymptotic result is
asserted here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K]

/-- The literal Artin--Schreier polynomial of the source auxiliary
coordinate. -/
noncomputable def stepAuxiliaryPolynomial
    (x : K) : K[X] :=
  X ^ 16 + (X - C (x ^ 17))

theorem stepAuxiliaryPolynomial_monic
    (x : K) : (stepAuxiliaryPolynomial x).Monic := by
  rw [stepAuxiliaryPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : K[X]) - C (x ^ 17)).degree ≤
        max (X : K[X]).degree (C (x ^ 17)).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) := max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : K[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num

@[simp]
theorem stepAuxiliaryPolynomial_natDegree
    (x : K) : (stepAuxiliaryPolynomial x).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [stepAuxiliaryPolynomial, degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := K) 16
  · calc
      ((X : K[X]) - C (x ^ 17)).degree ≤
          max (X : K[X]).degree (C (x ^ 17)).degree :=
        degree_sub_le _ _
      _ ≤ (1 : WithBot ℕ) := max_le (by simp) (degree_C_le.trans (by norm_num))
      _ < ((X : K[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num

variable [Algebra F256 K]

/-- The actual auxiliary coordinate is a root of its literal source
polynomial. -/
theorem stepAuxiliaryPolynomial_aeval
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (stepAuxiliaryCoordinate P x hx)
        (stepAuxiliaryPolynomial x) = 0 := by
  rw [stepAuxiliaryPolynomial, map_add, map_pow, aeval_X, map_sub, aeval_C]
  rw [Polynomial.aeval_X]
  change
    stepAuxiliaryCoordinate P x hx ^ 16 +
        (stepAuxiliaryCoordinate P x hx -
          stepFieldEmbedding P x hx (x ^ 17)) = 0
  rw [map_pow]
  linear_combination stepAuxiliaryCoordinate_artinSchreier P x hx

private theorem stepReciprocalRoot_eq_div_auxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepReciprocalRoot P x hx =
      stepFieldEmbedding P x hx x / stepAuxiliaryCoordinate P x hx := by
  have hx0 : stepFieldEmbedding P x hx x ≠ 0 := by
    have hxK : x ≠ 0 := by
      intro hzero
      subst x
      simp [GlobalPlace.order] at hx
    have hport := (stepFieldEmbedding P x hx).injective.ne hxK
    simp only [map_zero] at hport ⊢
    exact hport
  have hw0 := stepReciprocalRoot_ne_zero P x hx
  rw [stepAuxiliaryCoordinate]
  field_simp [hx0, hw0]

/-- The source auxiliary coordinate itself generates the degree-sixteen step
field over the preceding level. -/
theorem stepAuxiliaryCoordinate_adjoin_eq_top
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IntermediateField.adjoin K
        ({stepAuxiliaryCoordinate P x hx} : Set (StepField P x hx)) =
      (⊤ : IntermediateField K (StepField P x hx)) := by
  let w := stepReciprocalRoot P x hx
  let z := stepAuxiliaryCoordinate P x hx
  have hwAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (StepField P x hx)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (stepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [w, stepReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hwAdjoin : IntermediateField.adjoin K
      ({w} : Set (StepField P x hx)) =
      (⊤ : IntermediateField K (StepField P x hx)) :=
    IntermediateField.adjoin_eq_top_of_algebra K
      ({w} : Set (StepField P x hx)) hwAlgebraAdjoin
  have hwMem : w ∈ IntermediateField.adjoin K
      ({z} : Set (StepField P x hx)) := by
    dsimp only [w, z]
    rw [stepReciprocalRoot_eq_div_auxiliaryCoordinate P x hx]
    exact div_mem (algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self K z)
  apply top_unique
  rw [← hwAdjoin]
  exact IntermediateField.adjoin_simple_le_iff.mpr hwMem

/-- The minimal polynomial of the actual auxiliary coordinate is the literal
Artin--Schreier polynomial. -/
theorem minpoly_stepAuxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly K (stepAuxiliaryCoordinate P x hx) =
      stepAuxiliaryPolynomial x := by
  have hzIntegral : IsIntegral K (stepAuxiliaryCoordinate P x hx) :=
    IsIntegral.of_finite K _
  have hminDegree :
      (minpoly K (stepAuxiliaryCoordinate P x hx)).natDegree = 16 := by
    have hprimitive :=
      (Field.primitive_element_iff_minpoly_natDegree_eq K
        (stepAuxiliaryCoordinate P x hx)).mp
        (stepAuxiliaryCoordinate_adjoin_eq_top P x hx)
    simpa only [stepField_finrank P x hx] using hprimitive
  symm
  exact eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hzIntegral)
    (stepAuxiliaryPolynomial_monic x)
    (minpoly.dvd K (stepAuxiliaryCoordinate P x hx)
      (stepAuxiliaryPolynomial_aeval P x hx))
    (by rw [stepAuxiliaryPolynomial_natDegree, hminDegree])

theorem stepAuxiliaryPolynomial_irreducible
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Irreducible (stepAuxiliaryPolynomial x) := by
  rw [← minpoly_stepAuxiliaryCoordinate P x hx]
  exact minpoly.irreducible (IsIntegral.of_finite K _)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
