import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-!
# The characteristic polynomial of constant-field Frobenius

The Cartwright--Steger local norm calculation needs more than the order of
Frobenius.  This file uses the normal-basis theorem to prove that Frobenius
acts as one full cycle and hence has characteristic polynomial `X^d - 1`.
No matrix normal form is supplied by a caller.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

abbrev ConstantGaloisGroup (P : BasePrime) (r : Rank) :=
  (ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r)

/-- The additive Frobenius-difference operator whose image is the residue
hyperplane underlying the Cartwright--Steger color-one generators. -/
noncomputable def frobeniusDifferenceLinearMap
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r :=
  LinearMap.id - (constantFrobenius P r).symm.toLinearEquiv.toLinearMap

/-- The Frobenius-difference hyperplane. -/
noncomputable def frobeniusDifferenceRange
    (P : BasePrime) (r : Rank) :
    Submodule (BaseField P) (ConstantExtension P r) :=
  LinearMap.range (frobeniusDifferenceLinearMap P r)

theorem frobeniusDifferenceLinearMap_one
    (P : BasePrime) (r : Rank) :
    frobeniusDifferenceLinearMap P r 1 = 0 := by
  simp [frobeniusDifferenceLinearMap]

/-- The Frobenius-difference range is a proper subspace. -/
theorem frobeniusDifferenceRange_ne_top
    (P : BasePrime) (r : Rank) :
    frobeniusDifferenceRange P r ≠ ⊤ := by
  intro htop
  have hsurjective : Function.Surjective
      (frobeniusDifferenceLinearMap P r) := by
    rw [← LinearMap.range_eq_top]
    exact htop
  have hinjective : Function.Injective
      (frobeniusDifferenceLinearMap P r) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr
      hsurjective
  have hone : (1 : ConstantExtension P r) = 0 := by
    apply hinjective
    rw [frobeniusDifferenceLinearMap_one]
    simp [frobeniusDifferenceLinearMap]
  exact one_ne_zero hone

/-- Multiplication by a constant-field element, viewed over the base field. -/
noncomputable def constantMultiplicationLinearMap
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r where
  toFun x := a * x
  map_add' x y := by simp [mul_add]
  map_smul' c x := by
    simp [Algebra.smul_def, mul_comm, mul_assoc]

@[simp]
theorem constantMultiplicationLinearMap_apply
    (P : BasePrime) (r : Rank)
    (a x : ConstantExtension P r) :
    constantMultiplicationLinearMap P r a x = a * x :=
  rfl

/-- Only Frobenius-fixed scalars can preserve the Frobenius-difference
hyperplane under multiplication. -/
theorem eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r)
    (hstable : (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r) :
    (constantFrobenius P r).symm a = a := by
  let σ := (constantFrobenius P r).symm
  let H := frobeniusDifferenceRange P r
  have hterm : ∀ x : ConstantExtension P r,
      (a - σ a) * σ x ∈ H := by
    intro x
    have hdiff : frobeniusDifferenceLinearMap P r (a * x) ∈ H :=
      ⟨a * x, rfl⟩
    have hx : frobeniusDifferenceLinearMap P r x ∈ H := ⟨x, rfl⟩
    have hmul : a * frobeniusDifferenceLinearMap P r x ∈ H := by
      exact hstable (Submodule.mem_map_of_mem hx)
    have hsub := H.sub_mem hdiff hmul
    simpa [H, σ, frobeniusDifferenceLinearMap, map_mul,
      mul_sub, sub_mul] using hsub
  by_contra hne
  have hc : a - σ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  apply frobeniusDifferenceRange_ne_top P r
  apply top_unique
  intro y _
  let x : ConstantExtension P r :=
    constantFrobenius P r ((a - σ a)⁻¹ * y)
  have hx := hterm x
  simpa [H, x, σ, hc, mul_assoc] using hx

theorem exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r)
    (hstable : (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r) :
    ∃ c : BaseField P,
      a = algebraMap (BaseField P) (ConstantExtension P r) c := by
  have hsymm :=
    eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le P r a hstable
  have hforward : constantFrobenius P r a = a := by
    have h := congrArg (constantFrobenius P r) hsymm
    simpa using h.symm
  obtain ⟨c, hc⟩ :=
    exists_eq_algebraMap_of_constantFrobenius_eq P r a hforward
  exact ⟨c, hc.symm⟩

/-- In the fixed constant-field basis, `1 - Frobenius⁻¹` is exactly the
Frobenius-difference linear map. -/
theorem toLin_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (1 - ((frobeniusGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P))) =
      frobeniusDifferenceLinearMap P r := by
  have hinv : Matrix.toLin (constantBasis P r) (constantBasis P r)
      ((frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹) =
      (constantFrobenius P r).symm.toLinearEquiv.toLinearMap := by
    have hF : Matrix.toLin (constantBasis P r) (constantBasis P r)
        (frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
        (constantFrobenius P r).toLinearEquiv.toLinearMap := by
      rw [frobeniusGL_coe, Matrix.toLin_toMatrix]
    ext x
    apply (constantFrobenius P r).injective
    rw [show constantFrobenius P r
        ((constantFrobenius P r).symm.toLinearEquiv.toLinearMap x) = x by
      exact (constantFrobenius P r).apply_symm_apply x]
    change (constantFrobenius P r).toLinearEquiv.toLinearMap
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹) x) = x
    rw [← hF]
    rw [← Matrix.toLin_mul_apply]
    rw [show (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) *
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹ = 1 by
      rw [← Matrix.GeneralLinearGroup.coe_inv]
      exact congrArg Units.val (mul_inv_cancel (frobeniusGL P r))]
    rw [Matrix.toLin_one, LinearMap.id_apply]
  rw [map_sub, Matrix.toLin_one]
  rw [Matrix.GeneralLinearGroup.coe_inv, hinv]
  rfl

/-- The regular matrix of a constant is the matrix of multiplication by that
constant in the fixed constant-field basis. -/
theorem toLin_constantRegularMatrix
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (constantRegularMatrix P r a) =
      constantMultiplicationLinearMap P r a := by
  rw [constantRegularMatrix, Algebra.leftMulMatrix_apply,
    Matrix.toLin_toMatrix]
  rfl

/-- The matrix `1 - Frobenius⁻¹` has precisely the Frobenius-difference
hyperplane as its image. -/
theorem range_toLin_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (1 - ((frobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)))) =
      frobeniusDifferenceRange P r := by
  rw [toLin_one_sub_frobeniusGL_inv]
  rfl

/-- Constant conjugation transports the image of `1 - Frobenius⁻¹` to
the corresponding multiplicative translate of the Frobenius-difference
hyperplane. -/
theorem range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (constantRegularMatrix P r (u : ConstantExtension P r) *
            (1 - ((frobeniusGL P r)⁻¹ :
              Matrix.GeneralLinearGroup
                (Fin r.matrixRank) (BaseField P))) *
            constantRegularMatrix P r
              ((u : ConstantExtension P r)⁻¹))) =
      (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r u) := by
  rw [Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
      (constantBasis P r),
    Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
      (constantBasis P r),
    toLin_constantRegularMatrix, toLin_constantRegularMatrix,
    toLin_one_sub_frobeniusGL_inv]
  let U : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := constantMultiplicationLinearMap P r u
  let B : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := frobeniusDifferenceLinearMap P r
  let V : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := constantMultiplicationLinearMap P r
        ((u : ConstantExtension P r)⁻¹)
  change LinearMap.range (U.comp (B.comp V)) =
    (frobeniusDifferenceRange P r).map U
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y : ConstantExtension P r, rfl⟩
    refine ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y : ConstantExtension P r, rfl⟩, rfl⟩
    refine ⟨(u : ConstantExtension P r) * y, ?_⟩
    simp [U, B, V, LinearMap.comp_apply,
      constantMultiplicationLinearMap]

/-- Right multiplication by an invertible residue matrix does not change a
matrix's image subspace. -/
theorem range_toLin_mul_generalLinear
    (P : BasePrime) (r : Rank)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))
    (C : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BaseField P)) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (A * (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BaseField P)))) =
      LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r) A) := by
  rw [Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
    (constantBasis P r)]
  apply LinearMap.range_comp_of_range_eq_top
  rw [LinearMap.range_eq_top]
  intro x
  refine ⟨Matrix.toLin (constantBasis P r) (constantBasis P r)
    ((C⁻¹ : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BaseField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) x, ?_⟩
  rw [← Matrix.toLin_mul_apply]
  simp

/-- Enumerate the constant-field Galois group by the powers of arithmetic
Frobenius in the canonical range `0, ..., d-1`. -/
noncomputable def frobeniusPowerMap (P : BasePrime) (r : Rank) :
    Fin r.matrixRank → ConstantGaloisGroup P r :=
  fun i => constantFrobenius P r ^ i.val

theorem frobeniusPowerMap_injective (P : BasePrime) (r : Rank) :
    Function.Injective (frobeniusPowerMap P r) := by
  have aux : ∀ {i j : Fin r.matrixRank}, i.val ≤ j.val →
      frobeniusPowerMap P r i = frobeniusPowerMap P r j → i = j := by
    intro i j hle hij
    change constantFrobenius P r ^ i.val =
      constantFrobenius P r ^ j.val at hij
    have hpow : constantFrobenius P r ^ (j.val - i.val) = 1 := by
      apply mul_left_cancel (a := constantFrobenius P r ^ i.val)
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hle]
      rw [mul_one, hij]
    have hdvd : r.matrixRank ∣ j.val - i.val := by
      simpa [constantFrobenius_order P r] using
        (orderOf_dvd_of_pow_eq_one hpow)
    have hlt : j.val - i.val < r.matrixRank :=
      lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    have hzero : j.val - i.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero))
  intro i j hij
  rcases le_total i.val j.val with hle | hle
  · exact aux hle hij
  · exact (aux hle hij.symm).symm

theorem frobeniusPowerMap_bijective (P : BasePrime) (r : Rank) :
    Function.Bijective (frobeniusPowerMap P r) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨frobeniusPowerMap_injective P r, ?_⟩
  rw [Fintype.card_fin, Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank]
  exact (GaloisField.finrank P.q
    (by cases r <;> norm_num : r.matrixRank ≠ 0)).symm

/-- The canonical power enumeration as an equivalence. -/
noncomputable def frobeniusPowerEquiv (P : BasePrime) (r : Rank) :
    Fin r.matrixRank ≃ ConstantGaloisGroup P r :=
  Equiv.ofBijective (frobeniusPowerMap P r)
    (frobeniusPowerMap_bijective P r)

@[simp] theorem frobeniusPowerEquiv_apply
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    frobeniusPowerEquiv P r i = constantFrobenius P r ^ i.val :=
  rfl

/-- A normal basis ordered by consecutive powers of Frobenius. -/
noncomputable def frobeniusNormalBasis (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank) (BaseField P) (ConstantExtension P r) :=
  (IsGalois.normalBasis (BaseField P) (ConstantExtension P r)).reindex
    (frobeniusPowerEquiv P r).symm

theorem frobeniusNormalBasis_apply (P : BasePrime) (r : Rank)
    (i : Fin r.matrixRank) :
    frobeniusNormalBasis P r i =
      (constantFrobenius P r ^ i.val)
        (IsGalois.normalBasis (BaseField P) (ConstantExtension P r) 1) := by
  rw [frobeniusNormalBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm, frobeniusPowerEquiv_apply,
    IsGalois.normalBasis_apply]

theorem constantFrobenius_frobeniusNormalBasis
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    constantFrobenius P r (frobeniusNormalBasis P r i) =
      frobeniusNormalBasis P r (finRotate r.matrixRank i) := by
  rw [frobeniusNormalBasis_apply, frobeniusNormalBasis_apply,
    finRotate_apply]
  change ((constantFrobenius P r) *
      (constantFrobenius P r) ^ i.val)
        (IsGalois.normalBasis (BaseField P) (ConstantExtension P r) 1) = _
  rw [← pow_succ']
  cases r with
  | three =>
      fin_cases i
      · simp
      · simp
      · simpa using congrArg
          (fun e : ConstantGaloisGroup P .three =>
            e (IsGalois.normalBasis (BaseField P)
              (ConstantExtension P .three) 1))
          (constantFrobenius_pow_matrixRank P .three)
  | four =>
      fin_cases i
      · simp
      · simp
      · simp
      · simpa using congrArg
          (fun e : ConstantGaloisGroup P .four =>
            e (IsGalois.normalBasis (BaseField P)
              (ConstantExtension P .four) 1))
          (constantFrobenius_pow_matrixRank P .four)

/-- Frobenius in the rank-three consecutive normal basis is the explicit
three-cycle matrix. -/
theorem constantFrobenius_toMatrix_normalBasis_three (P : BasePrime) :
    LinearMap.toMatrix (frobeniusNormalBasis P .three)
        (frobeniusNormalBasis P .three)
        (constantFrobenius P .three).toLinearEquiv.toLinearMap =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  have hrot : (finRotate 3 : Fin 3 → Fin 3) = ![1, 2, 0] := by
    funext i
    fin_cases i <;> native_decide
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (frobeniusNormalBasis P .three).repr
    (constantFrobenius P .three (frobeniusNormalBasis P .three j)) i = _
  rw [constantFrobenius_frobeniusNormalBasis]
  rw [(frobeniusNormalBasis P .three).repr_self]
  rw [Finsupp.single_apply]
  erw [hrot]
  fin_cases i <;> fin_cases j <;> rfl

/-- Frobenius in the rank-four consecutive normal basis is the explicit
four-cycle matrix. -/
theorem constantFrobenius_toMatrix_normalBasis_four (P : BasePrime) :
    LinearMap.toMatrix (frobeniusNormalBasis P .four)
        (frobeniusNormalBasis P .four)
        (constantFrobenius P .four).toLinearEquiv.toLinearMap =
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] := by
  have hrot : (finRotate 4 : Fin 4 → Fin 4) = ![1, 2, 3, 0] := by
    funext i
    fin_cases i <;> native_decide
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (frobeniusNormalBasis P .four).repr
    (constantFrobenius P .four (frobeniusNormalBasis P .four j)) i = _
  rw [constantFrobenius_frobeniusNormalBasis]
  rw [(frobeniusNormalBasis P .four).repr_self]
  rw [Finsupp.single_apply]
  erw [hrot]
  fin_cases i <;> fin_cases j <;> rfl

private theorem normalCycle_three_charpoly (K : Type*) [Field K] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).charpoly =
      Polynomial.X ^ 3 - (1 : Polynomial K) := by
  rw [Matrix.charpoly]
  simp [Matrix.det_fin_three]
  ring

private theorem normalCycle_four_charpoly (K : Type*) [Field K] :
    (!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
      Matrix (Fin 4) (Fin 4) K).charpoly =
      Polynomial.X ^ 4 - (1 : Polynomial K) := by
  rw [Matrix.charpoly]
  have hmatrix :
      (!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
        Matrix (Fin 4) (Fin 4) K).charmatrix =
      !![Polynomial.X, 0, 0, -1; -1, Polynomial.X, 0, 0;
        0, -1, Polynomial.X, 0; 0, 0, -1, Polynomial.X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]
  rw [hmatrix]
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Fin.sum_univ_four]
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [h31, h32]
  simp
  ring

set_option maxHeartbeats 800000 in
theorem frobeniusGL_charpoly_three (P : BasePrime) :
    (frobeniusGL P .three : Matrix (Fin Rank.three.matrixRank)
      (Fin Rank.three.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.three.matrixRank -
        (1 : Polynomial (BaseField P)) := by
  rw [frobeniusGL_coe]
  calc
    _ = LinearMap.charpoly
        (constantFrobenius P .three).toLinearEquiv.toLinearMap :=
      (LinearMap.charpoly_toMatrix
        (constantFrobenius P .three).toLinearEquiv.toLinearMap
        (constantBasis P .three))
    _ = (LinearMap.toMatrix (frobeniusNormalBasis P .three)
          (frobeniusNormalBasis P .three)
          (constantFrobenius P .three).toLinearEquiv.toLinearMap).charpoly :=
      (LinearMap.charpoly_toMatrix _ _).symm
    _ = _ := by rw [constantFrobenius_toMatrix_normalBasis_three]
                exact normalCycle_three_charpoly (BaseField P)

set_option maxHeartbeats 800000 in
theorem frobeniusGL_charpoly_four (P : BasePrime) :
    (frobeniusGL P .four : Matrix (Fin Rank.four.matrixRank)
      (Fin Rank.four.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.four.matrixRank -
        (1 : Polynomial (BaseField P)) := by
  rw [frobeniusGL_coe]
  calc
    _ = LinearMap.charpoly
        (constantFrobenius P .four).toLinearEquiv.toLinearMap :=
      (LinearMap.charpoly_toMatrix
        (constantFrobenius P .four).toLinearEquiv.toLinearMap
        (constantBasis P .four))
    _ = (LinearMap.toMatrix (frobeniusNormalBasis P .four)
          (frobeniusNormalBasis P .four)
          (constantFrobenius P .four).toLinearEquiv.toLinearMap).charpoly :=
      (LinearMap.charpoly_toMatrix _ _).symm
    _ = _ := by rw [constantFrobenius_toMatrix_normalBasis_four]
                exact normalCycle_four_charpoly (BaseField P)

/-- Arithmetic Frobenius has the full-cycle characteristic polynomial in
the fixed construction basis. -/
theorem frobeniusGL_charpoly (P : BasePrime) (r : Rank) :
    (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ r.matrixRank - 1 := by
  cases r with
  | three => exact frobeniusGL_charpoly_three P
  | four => exact frobeniusGL_charpoly_four P

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
