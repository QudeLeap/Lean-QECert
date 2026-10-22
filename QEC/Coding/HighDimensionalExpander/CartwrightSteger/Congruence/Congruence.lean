import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-!
# Congruence evaluation for the Cartwright--Steger hierarchy

This file constructs the actual residue map from
`F_q[y, 1/y, 1/(1+y)]` to the selected finite hierarchy field.  The map is
proved surjective from the primitive-element property of the internally
selected image of `y`; no residue map or lifting certificate is accepted from
a caller.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- Polynomial evaluation at the construction-owned congruence value of
`y`. -/
noncomputable def indexPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* ResidueField P r level :=
  (Polynomial.aeval (indexPlaceY P r level)).toRingHom

@[simp] theorem indexPolynomialEval_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPolynomialEval P r level Polynomial.X =
      indexPlaceY P r level := by
  simp [indexPolynomialEval]

@[simp] theorem indexPolynomialEval_one_add_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPolynomialEval P r level (1 + Polynomial.X) =
      1 + indexPlaceY P r level := by
  simp [indexPolynomialEval]

theorem indexPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [map_mul, indexPolynomialEval_X, indexPolynomialEval_one_add_X,
    isUnit_iff_ne_zero]
  exact mul_ne_zero (indexPlaceY_ne_zero P r level)
    (indexPlaceY_one_add_ne_zero P r level)

/-- The genuine congruence evaluation on the localized arithmetic ring. -/
noncomputable def indexArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* ResidueField P r level :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
    (S := ArithmeticRing P)
    (g := indexPolynomialEval P r level)
    (indexPolynomialEval_denominator_isUnit P r level)

@[simp] theorem indexArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    indexArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      indexPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- Polynomial evaluation is onto because the selected image of `y`
generates the complete residue field over `F_q`. -/
theorem indexPolynomialEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexPolynomialEval P r level) := by
  change Function.Surjective
    ((Polynomial.aeval (indexPlaceY P r level) :
      PolynomialRing P →ₐ[BaseField P] ResidueField P r level).toRingHom)
  have hRange :
      (Polynomial.aeval (indexPlaceY P r level) :
        PolynomialRing P →ₐ[BaseField P]
          ResidueField P r level).range = ⊤ := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (indexPlaceY P r level))
      (indexPlaceY_adjoin_eq_top P r level)
  exact (AlgHom.range_eq_top _).mp hRange

/-- The localized congruence map is onto; polynomial representatives already
hit every residue-field element. -/
theorem indexArithmeticEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexArithmeticEval P r level) := by
  intro x
  obtain ⟨f, rfl⟩ := indexPolynomialEval_surjective P r level x
  exact ⟨algebraMap (PolynomialRing P) (ArithmeticRing P) f,
    indexArithmeticEval_algebraMap P r level f⟩

/-- The selected congruence ideal is the kernel of the constructed residue
map. -/
noncomputable def IndexCongruenceIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    Ideal (ArithmeticRing P) :=
  RingHom.ker (indexArithmeticEval P r level)

/-- First isomorphism theorem for the actual selected congruence ideal. -/
noncomputable def indexArithmeticQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P ⧸ IndexCongruenceIdeal P r level ≃+*
      ResidueField P r level :=
  RingHom.quotientKerEquivOfSurjective
    (indexArithmeticEval_surjective P r level)

namespace CongruenceLifting

open Matrix

private theorem property_six_mul
    {M : Type*} [Monoid M] (Q : M → Prop)
    (hmul : ∀ a b, Q a → Q b → Q (a * b))
    {a b c d e f : M}
    (ha : Q a) (hb : Q b) (hc : Q c)
    (hd : Q d) (he : Q e) (hf : Q f) :
    Q (a * b * c * d * e * f) :=
  hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ha hb) hc) hd) he) hf

/-- Column-update formula at the field structure used by the finite computations. -/
private theorem field_mul_transvection_apply
    {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (i j row col : Fin n) (c : K) :
    (M * transvection i j c) row col =
      if col = j then M row j + c * M row i else M row col := by
  by_cases h : col = j
  · subst col
    rw [if_pos rfl]
    exact Matrix.mul_transvection_apply_same i j row c M
  · rw [if_neg h]
    exact Matrix.mul_transvection_apply_of_ne i j row col h c M

private theorem fin3_pair02_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (0 : Fin 3) (2 : Fin 3) a *
      transvection (2 : Fin 3) (0 : Fin 3) (-a⁻¹) *
      transvection (0 : Fin 3) (2 : Fin 3) a *
      transvection (0 : Fin 3) (2 : Fin 3) (-1) *
      transvection (2 : Fin 3) (0 : Fin 3) 1 *
      transvection (0 : Fin 3) (2 : Fin 3) (-1) =
        diagonal ![a, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]

private theorem fin3_pair12_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (1 : Fin 3) (2 : Fin 3) a *
      transvection (2 : Fin 3) (1 : Fin 3) (-a⁻¹) *
      transvection (1 : Fin 3) (2 : Fin 3) a *
      transvection (1 : Fin 3) (2 : Fin 3) (-1) *
      transvection (2 : Fin 3) (1 : Fin 3) 1 *
      transvection (1 : Fin 3) (2 : Fin 3) (-1) =
        diagonal ![1, a, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]

private theorem fin3_diagonal_eq_pair_product
    {K : Type*} [Field K] (D : Fin 3 → K)
    (hdet : Matrix.det (diagonal D) = 1) :
    diagonal D =
      diagonal ![D 0, 1, (D 0)⁻¹] *
        diagonal ![1, D 1, (D 1)⁻¹] := by
  have hprod : D 0 * (D 1 * D 2) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 = (D 0)⁻¹ * (D 1)⁻¹ := by
    apply (mul_left_cancel₀ (mul_ne_zero h0 h1))
    calc
      (D 0 * D 1) * D 2 = 1 := by simpa [mul_assoc] using hprod
      _ = (D 0 * D 1) * ((D 0)⁻¹ * (D 1)⁻¹) := by
        field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h2]

private theorem fin4_pair03_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (0 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (0 : Fin 4) (-a⁻¹) *
      transvection (0 : Fin 4) (3 : Fin 4) a *
      transvection (0 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (0 : Fin 4) 1 *
      transvection (0 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![a, 1, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]

private theorem fin4_pair13_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (1 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (1 : Fin 4) (-a⁻¹) *
      transvection (1 : Fin 4) (3 : Fin 4) a *
      transvection (1 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (1 : Fin 4) 1 *
      transvection (1 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![1, a, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]

private theorem fin4_pair23_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (2 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (2 : Fin 4) (-a⁻¹) *
      transvection (2 : Fin 4) (3 : Fin 4) a *
      transvection (2 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (2 : Fin 4) 1 *
      transvection (2 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![1, 1, a, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]

private theorem fin4_diagonal_eq_pair_product
    {K : Type*} [Field K] (D : Fin 4 → K)
    (hdet : Matrix.det (diagonal D) = 1) :
    diagonal D =
      diagonal ![D 0, 1, 1, (D 0)⁻¹] *
        diagonal ![1, D 1, 1, (D 1)⁻¹] *
          diagonal ![1, 1, D 2, (D 2)⁻¹] := by
  have hprod : D 0 * (D 1 * (D 2 * D 3)) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h3 : D 3 = (D 0)⁻¹ * (D 1)⁻¹ * (D 2)⁻¹ := by
    apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h0 h1) h2))
    calc
      (D 0 * D 1 * D 2) * D 3 = 1 := by
        simpa [mul_assoc] using hprod
      _ = (D 0 * D 1 * D 2) *
          ((D 0)⁻¹ * (D 1)⁻¹ * (D 2)⁻¹) := by
        field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h3]

theorem property_fin3_diagonal
    {K : Type*} [Field K] (Q : Matrix (Fin 3) (Fin 3) K → Prop)
    (htrans : ∀ t : Matrix.TransvectionStruct (Fin 3) K, Q t.toMatrix)
    (hmul : ∀ A B, Q A → Q B → Q (A * B))
    (D : Fin 3 → K) (hdet : Matrix.det (diagonal D) = 1) :
    Q (diagonal D) := by
  have hprod : D 0 * (D 1 * D 2) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  rw [fin3_diagonal_eq_pair_product D hdet,
    ← fin3_pair02_factor (D 0) h0,
    ← fin3_pair12_factor (D 1) h1]
  apply hmul
  · exact property_six_mul Q hmul
      (htrans ⟨0, 2, by decide, D 0⟩)
      (htrans ⟨2, 0, by decide, -(D 0)⁻¹⟩)
      (htrans ⟨0, 2, by decide, D 0⟩)
      (htrans ⟨0, 2, by decide, -1⟩)
      (htrans ⟨2, 0, by decide, 1⟩)
      (htrans ⟨0, 2, by decide, -1⟩)
  · exact property_six_mul Q hmul
      (htrans ⟨1, 2, by decide, D 1⟩)
      (htrans ⟨2, 1, by decide, -(D 1)⁻¹⟩)
      (htrans ⟨1, 2, by decide, D 1⟩)
      (htrans ⟨1, 2, by decide, -1⟩)
      (htrans ⟨2, 1, by decide, 1⟩)
      (htrans ⟨1, 2, by decide, -1⟩)

theorem property_fin4_diagonal
    {K : Type*} [Field K] (Q : Matrix (Fin 4) (Fin 4) K → Prop)
    (htrans : ∀ t : Matrix.TransvectionStruct (Fin 4) K, Q t.toMatrix)
    (hmul : ∀ A B, Q A → Q B → Q (A * B))
    (D : Fin 4 → K) (hdet : Matrix.det (diagonal D) = 1) :
    Q (diagonal D) := by
  have hprod : D 0 * (D 1 * (D 2 * D 3)) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 ≠ 0 := by
    intro h
    simp [h] at hprod
  rw [fin4_diagonal_eq_pair_product D hdet,
    ← fin4_pair03_factor (D 0) h0,
    ← fin4_pair13_factor (D 1) h1,
    ← fin4_pair23_factor (D 2) h2]
  apply hmul
  · apply hmul
    · exact property_six_mul Q hmul
        (htrans ⟨0, 3, by decide, D 0⟩)
        (htrans ⟨3, 0, by decide, -(D 0)⁻¹⟩)
        (htrans ⟨0, 3, by decide, D 0⟩)
        (htrans ⟨0, 3, by decide, -1⟩)
        (htrans ⟨3, 0, by decide, 1⟩)
        (htrans ⟨0, 3, by decide, -1⟩)
    · exact property_six_mul Q hmul
        (htrans ⟨1, 3, by decide, D 1⟩)
        (htrans ⟨3, 1, by decide, -(D 1)⁻¹⟩)
        (htrans ⟨1, 3, by decide, D 1⟩)
        (htrans ⟨1, 3, by decide, -1⟩)
        (htrans ⟨3, 1, by decide, 1⟩)
        (htrans ⟨1, 3, by decide, -1⟩)
  · exact property_six_mul Q hmul
      (htrans ⟨2, 3, by decide, D 2⟩)
      (htrans ⟨3, 2, by decide, -(D 2)⁻¹⟩)
      (htrans ⟨2, 3, by decide, D 2⟩)
      (htrans ⟨2, 3, by decide, -1⟩)
      (htrans ⟨3, 2, by decide, 1⟩)
      (htrans ⟨2, 3, by decide, -1⟩)

/-- A surjective coefficient map to a field induces a surjection on
rank-three special linear groups. -/
theorem specialLinearMap_surjective_fin3
    {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 3) f) := by
  classical
  intro g
  let Q : Matrix (Fin 3) (Fin 3) K → Prop := fun M =>
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) R,
      f.mapMatrix a = M
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin 3) K, Q t.toMatrix := by
    intro t
    obtain ⟨c, hc⟩ := hf t.c
    let s : Matrix.SpecialLinearGroup (Fin 3) R :=
      ⟨Matrix.transvection t.i t.j c,
        Matrix.det_transvection_of_ne t.i t.j t.hij c⟩
    refine ⟨s, ?_⟩
    ext i j
    by_cases h : t.i = i ∧ t.j = j <;>
      simp [s, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
        Matrix.map_apply, Matrix.one_apply, h, hc]
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, f.mapMatrix.map_mul, ha, hb]
  have hQ : Q (g : Matrix (Fin 3) (Fin 3) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      apply property_fin3_diagonal Q htrans hmul D
      exact hD.trans g.prop
    · exact htrans
    · exact hmul
  obtain ⟨a, ha⟩ := hQ
  refine ⟨a, Subtype.ext ?_⟩
  exact ha

/-- A surjective coefficient map to a field induces a surjection on
rank-four special linear groups. -/
theorem specialLinearMap_surjective_fin4
    {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 4) f) := by
  classical
  intro g
  let Q : Matrix (Fin 4) (Fin 4) K → Prop := fun M =>
    ∃ a : Matrix.SpecialLinearGroup (Fin 4) R,
      f.mapMatrix a = M
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin 4) K, Q t.toMatrix := by
    intro t
    obtain ⟨c, hc⟩ := hf t.c
    let s : Matrix.SpecialLinearGroup (Fin 4) R :=
      ⟨Matrix.transvection t.i t.j c,
        Matrix.det_transvection_of_ne t.i t.j t.hij c⟩
    refine ⟨s, ?_⟩
    ext i j
    by_cases h : t.i = i ∧ t.j = j <;>
      simp [s, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
        Matrix.map_apply, Matrix.one_apply, h, hc]
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, f.mapMatrix.map_mul, ha, hb]
  have hQ : Q (g : Matrix (Fin 4) (Fin 4) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      apply property_fin4_diagonal Q htrans hmul D
      exact hD.trans g.prop
    · exact htrans
    · exact hmul
  obtain ⟨a, ha⟩ := hQ
  refine ⟨a, Subtype.ext ?_⟩
  exact ha

/-- Reduction on the rank-selected special linear group. -/
noncomputable def indexSpecialLinearReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (indexArithmeticEval P r level)

/-- Rank-specialized local lifting: reduction from the selected arithmetic
ring onto the finite residue field is surjective on special linear groups. -/
theorem indexSpecialLinearMap_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (indexSpecialLinearReduction P r level) := by
  cases r with
  | three =>
      exact specialLinearMap_surjective_fin3
        (indexArithmeticEval P .three level)
        (indexArithmeticEval_surjective P .three level)
  | four =>
      exact specialLinearMap_surjective_fin4
        (indexArithmeticEval P .four level)
        (indexArithmeticEval_surjective P .four level)

/-- The principal congruence subgroup in arithmetic `SL_d`. -/
noncomputable def IndexSpecialLinearCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P)) :=
  (indexSpecialLinearReduction P r level).ker

noncomputable instance indexSpecialLinearCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexSpecialLinearCongruenceSubgroup P r level).Normal := by
  dsimp [IndexSpecialLinearCongruenceSubgroup]
  infer_instance

/-- The arithmetic special-linear congruence quotient is exactly the finite
special linear group at the selected place. -/
noncomputable def indexSpecialLinearQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) ⧸
        IndexSpecialLinearCongruenceSubgroup P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (indexSpecialLinearReduction P r level)
    (indexSpecialLinearMap_surjective P r level)

/-- Reduction followed by projectivization, with the source living over the
actual localized arithmetic ring. -/
noncomputable def congruenceSpecialToProjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      PGL P r level :=
  (specialToProjective P r level).comp
    (indexSpecialLinearReduction P r level)

/-- Local lifting identifies the full projective special-linear residue image
with the reduction of arithmetic special-linear matrices. -/
theorem range_congruenceSpecialToProjective_eq_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (congruenceSpecialToProjective P r level).range = PSL P r level := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    exact ⟨indexSpecialLinearReduction P r level a, rfl⟩
  · rintro g ⟨s, rfl⟩
    obtain ⟨a, rfl⟩ := indexSpecialLinearMap_surjective P r level s
    exact ⟨a, rfl⟩

/-! ## A construction-owned lower bound for the finite PSL endpoint -/

/-- The first of two fixed coordinates in ranks three and four. -/
private def rankFirstIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, by cases r <;> decide⟩

/-- The second of two fixed coordinates in ranks three and four. -/
private def rankSecondIndex (r : Rank) : Fin r.matrixRank :=
  ⟨1, by cases r <;> decide⟩

private theorem rankFirstIndex_ne_rankSecondIndex (r : Rank) :
    rankFirstIndex r ≠ rankSecondIndex r := by
  cases r <;> decide

/-- A fixed root subgroup in the finite special linear group. -/
noncomputable def residueTransvectionSpecial
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  ⟨Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) c,
    Matrix.det_transvection_of_ne
      (rankFirstIndex r) (rankSecondIndex r)
      (rankFirstIndex_ne_rankSecondIndex r) c⟩

@[simp] theorem residueTransvectionSpecial_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) :
    (residueTransvectionSpecial P r level c :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) c :=
  rfl

private theorem residueTransvectionSpecial_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (c d : ResidueField P r level) :
    residueTransvectionSpecial P r level c *
        residueTransvectionSpecial P r level d =
      residueTransvectionSpecial P r level (c + d) := by
  classical
  apply Subtype.ext
  exact Matrix.transvection_mul_transvection_same
    (i := rankFirstIndex r) (j := rankSecondIndex r)
    (rankFirstIndex_ne_rankSecondIndex r) c d

/-- The fixed root subgroup, regarded as actual elements of `PSL`. -/
noncomputable def residueTransvectionPSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) : PSL P r level :=
  ⟨specialToProjective P r level
      (residueTransvectionSpecial P r level c),
    ⟨residueTransvectionSpecial P r level c, rfl⟩⟩

/-- Distinct residue-field parameters give distinct projective
transvections.  The proof rules out their quotient being a scalar matrix by
inspecting its fixed off-diagonal entry. -/
theorem residueTransvectionPSL_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (residueTransvectionPSL P r level) := by
  intro c d hcd
  have hprojective :
      specialToProjective P r level
          (residueTransvectionSpecial P r level c) =
        specialToProjective P r level
          (residueTransvectionSpecial P r level d) :=
    congrArg Subtype.val hcd
  have hmul :
      residueTransvectionSpecial P r level c *
          residueTransvectionSpecial P r level (d - c) =
        residueTransvectionSpecial P r level d := by
    rw [residueTransvectionSpecial_mul]
    congr 1
    abel
  have hprojective_zero :
      specialToProjective P r level
          (residueTransvectionSpecial P r level (d - c)) = 1 := by
    have hmapped := congrArg (specialToProjective P r level) hmul
    rw [map_mul, hprojective] at hmapped
    have hcancelled := congrArg
      (fun x =>
        ((specialToProjective P r level)
          (residueTransvectionSpecial P r level d))⁻¹ * x) hmapped
    simpa [mul_assoc] using hcancelled
  have hcenter :
      Matrix.SpecialLinearGroup.toGL
          (residueTransvectionSpecial P r level (d - c)) ∈
        Subgroup.center
          (Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa [specialToProjective] using hprojective_zero
  obtain ⟨a, ha⟩ :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter
  have hoffdiag := congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) =>
      M (rankFirstIndex r) (rankSecondIndex r)) ha
  have hdc : 0 = d - c := by
    change (Matrix.scalar (Fin r.matrixRank) a)
        (rankFirstIndex r) (rankSecondIndex r) =
      Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) (d - c)
        (rankFirstIndex r) (rankSecondIndex r) at hoffdiag
    simpa [residueTransvectionSpecial, Matrix.transvection,
      Matrix.scalar_apply, rankFirstIndex_ne_rankSecondIndex] using hoffdiag
  exact (sub_eq_zero.mp hdc.symm).symm

/-- The finite projective special-linear group has at least as many elements
as its residue field, with no cardinality formula imported as an assumption. -/
theorem natCard_residueField_le_natCard_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card (ResidueField P r level) ≤
      Nat.card (PSL P r level) := by
  classical
  let projectToPSL :
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ResidueField P r level) →
        PSL P r level := fun s =>
    ⟨specialToProjective P r level s, ⟨s, rfl⟩⟩
  have projectToPSL_surjective : Function.Surjective projectToPSL := by
    rintro ⟨g, s, rfl⟩
    exact ⟨s, rfl⟩
  letI : Finite (PSL P r level) :=
    Finite.of_surjective projectToPSL projectToPSL_surjective
  exact Nat.card_le_card_of_injective
    (residueTransvectionPSL P r level)
    (residueTransvectionPSL_injective P r level)

/-- The selected finite `PSL` endpoints are unbounded along the hierarchy. -/
theorem PSL_unbounded (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (PSL P r level) := by
  obtain ⟨level, hlevel⟩ := residueField_unbounded P r bound
  exact ⟨level, hlevel.trans_le
    (natCard_residueField_le_natCard_PSL P r level)⟩

end CongruenceLifting

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
