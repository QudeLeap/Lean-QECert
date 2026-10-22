import QEC.Coding.HighDimensionalExpander.Hecke.SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev

/-!
# Constructive preparation for the local Cartan decomposition

This module starts the matrix-reduction proof for the actual Laurent-series
local field.  Its first task is to clear all negative powers in a scalar or a
finite matrix by one explicitly constructed uniformizer power.  The resulting
integral matrix is the input to the Smith-normal-form stage; no integral model
or denominator bound is supplied by a caller.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.SphericalHecke

open scoped LocalTopology MatrixGroups Pointwise Valued
open Module

universe u

/-- The least exponent selected from the Laurent-series order that clears the
negative part of one scalar. -/
def integralClearingExponent
    {k : Type u} [Field k] (f : LocalFunctionField k) : ℕ :=
  Int.toNat (-f.order)

/-- Multiplication by the selected power of `X` places a Laurent series in
the actual valuation ring. -/
theorem integralClearingExponent_spec
    {k : Type u} [Field k] (f : LocalFunctionField k) :
    (uniformizerUnit k : LocalFunctionField k) ^ integralClearingExponent f * f ∈
      Valued.integer (LocalFunctionField k) := by
  rw [Valuation.mem_integer_iff]
  apply (LaurentSeries.val_le_one_iff_eq_coe k _).2
  by_cases h : f.order ≤ 0
  · refine ⟨f.powerSeriesPart, ?_⟩
    rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
    simp only [integralClearingExponent, Int.toNat_of_nonneg (neg_nonneg.mpr h),
      coe_uniformizerUnit, HahnSeries.single_pow, one_pow, nsmul_eq_mul,
      mul_one]
  · have hpos : 0 ≤ f.order := le_of_lt (lt_of_not_ge h)
    refine ⟨PowerSeries.X ^ Int.natAbs f.order * f.powerSeriesPart, ?_⟩
    rw [integralClearingExponent,
      Int.toNat_eq_zero.mpr (neg_nonpos.mpr hpos), pow_zero, one_mul]
    exact LaurentSeries.X_order_mul_powerSeriesPart
      (Int.natAbs_of_nonneg hpos)

/-- Every nonnegative uniformizer power belongs to the actual valuation
ring. -/
theorem uniformizer_pow_mem_integer
    {k : Type u} [Field k] (n : ℕ) :
    (uniformizerUnit k : LocalFunctionField k) ^ n ∈
      Valued.integer (LocalFunctionField k) := by
  rw [Valuation.mem_integer_iff]
  apply (LaurentSeries.val_le_one_iff_eq_coe k _).2
  exact ⟨PowerSeries.X ^ n, by simp [coe_uniformizerUnit]⟩

/-- Any exponent above the constructed clearing exponent also produces an
integral scalar. -/
theorem scaled_mem_integer_of_clearingExponent_le
    {k : Type u} [Field k] (f : LocalFunctionField k) {n : ℕ}
    (h : integralClearingExponent f ≤ n) :
    (uniformizerUnit k : LocalFunctionField k) ^ n * f ∈
      Valued.integer (LocalFunctionField k) := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact (Valued.integer (LocalFunctionField k)).mul_mem
    (uniformizer_pow_mem_integer (n - integralClearingExponent f))
    (integralClearingExponent_spec f)

/-- One exponent that simultaneously clears every entry of a finite square
matrix. -/
def matrixClearingExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) : ℕ :=
  Finset.univ.sup fun i =>
    Finset.univ.sup fun j => integralClearingExponent (A i j)

theorem integralClearingExponent_le_matrixClearingExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    integralClearingExponent (A i j) ≤ matrixClearingExponent A := by
  apply le_trans (Finset.le_sup (f := fun j : Fin d =>
    integralClearingExponent (A i j)) (Finset.mem_univ j))
  exact Finset.le_sup (f := fun i : Fin d => Finset.univ.sup fun j =>
    integralClearingExponent (A i j)) (Finset.mem_univ i)

/-- Scaling by `matrixClearingExponent` places every matrix entry in the
valuation ring. -/
theorem matrix_scaled_entry_mem_integer
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j ∈
      Valued.integer (LocalFunctionField k) :=
  scaled_mem_integer_of_clearingExponent_le (A i j)
    (integralClearingExponent_le_matrixClearingExponent A i j)

/-! ## The integral matrix and its full-rank image -/

/-- The matrix over the valuation ring obtained by multiplying every entry by
one construction-owned uniformizer power. -/
def clearedMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (Valued.integer (LocalFunctionField k)) :=
  fun i j =>
    ⟨(uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j,
      matrix_scaled_entry_mem_integer A i j⟩

@[simp]
theorem coe_clearedMatrix_apply
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    ((clearedMatrix A i j : Valued.integer (LocalFunctionField k)) :
      LocalFunctionField k) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j :=
  rfl

/-- Base-changing the cleared matrix back to the local field recovers the
uniformizer scalar multiple of the original matrix. -/
theorem map_clearedMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    (SubringClass.subtype (Valued.integer (LocalFunctionField k))).mapMatrix
        (clearedMatrix A) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A • A := by
  ext i j
  simp [clearedMatrix, smul_eq_mul]

/-- Clearing denominators in an invertible matrix does not destroy its
nonzero determinant over the valuation ring. -/
theorem clearedMatrix_det_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (clearedMatrix (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).det ≠ 0 := by
  intro hdet
  have hmap := congrArg
    (SubringClass.subtype (Valued.integer (LocalFunctionField k))) hdet
  rw [map_zero, RingHom.map_det, map_clearedMatrix, Matrix.det_smul] at hmap
  have hu : (uniformizerUnit k : LocalFunctionField k) ≠ 0 := Units.ne_zero _
  have hupow :
      ((uniformizerUnit k : LocalFunctionField k) ^
        matrixClearingExponent
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) ^
            Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hu)
  exact (mul_ne_zero hupow A.det_ne_zero) hmap

/-- The power series representing one entry of the cleared matrix.  It is
obtained through the proved equivalence between `k[[X]]` and the actual
valuation ring, so this definition carries no caller-provided integral
representation. -/
def clearedPowerSeriesEntry
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    IntegerRing k :=
  (LocalTopology.powerSeriesIntegerEquiv k).symm
    (clearedMatrix (k := k) (d := d) A i j)

theorem coe_clearedPowerSeriesEntry
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j =
      HahnSeries.ofPowerSeries Int k
        (clearedPowerSeriesEntry (k := k) (d := d) A i j) :=
  (congrArg Subtype.val
    ((LocalTopology.powerSeriesIntegerEquiv k).apply_symm_apply
      (clearedMatrix (k := k) (d := d) A i j))).symm

/-- The same cleared matrix, represented in the concrete DVR `k[[X]]` used by
the Smith-normal-form library. -/
def clearedPowerSeriesMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (IntegerRing k) :=
  fun i j => clearedPowerSeriesEntry (k := k) (d := d) A i j

/-- Embedding the concrete power-series matrix into `k((X))` recovers the
same scalar multiple of the original matrix. -/
theorem map_clearedPowerSeriesMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    (HahnSeries.ofPowerSeries Int k).mapMatrix
        (clearedPowerSeriesMatrix (k := k) (d := d) A) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A • A := by
  apply Matrix.ext
  intro i j
  change HahnSeries.ofPowerSeries Int k
      (clearedPowerSeriesEntry (k := k) (d := d) A i j) =
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j
  exact (coe_clearedPowerSeriesEntry (k := k) (d := d) A i j).symm

/-- The concrete cleared power-series matrix has nonzero determinant. -/
theorem clearedPowerSeriesMatrix_det_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).det ≠ 0 := by
  intro hdet
  have hmap := congrArg (HahnSeries.ofPowerSeries Int k) hdet
  rw [map_zero, RingHom.map_det, map_clearedPowerSeriesMatrix, Matrix.det_smul] at hmap
  have hu : (uniformizerUnit k : LocalFunctionField k) ≠ 0 := Units.ne_zero _
  have hupow :
      ((uniformizerUnit k : LocalFunctionField k) ^
        matrixClearingExponent
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) ^
            Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hu)
  exact (mul_ne_zero hupow A.det_ne_zero) hmap

/-- The cleared power-series matrix acts injectively on the standard integral
lattice. -/
theorem clearedPowerSeriesMatrix_mulVec_injective
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ∀ x y : Fin d → IntegerRing k,
      Matrix.mulVec
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) x =
        Matrix.mulVec
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) y →
      x = y := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (clearedPowerSeriesMatrix_det_ne_zero (k := k) (d := d) A)
  rw [Matrix.mulVec_sub, hxy, sub_self]

/-- The image lattice of the cleared matrix has the full rank required by
Smith normal form.  This rank fact is proved from invertibility rather than
accepted as an input hypothesis. -/
theorem clearedPowerSeriesMatrix_range_finrank
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Module.finrank (IntegerRing k)
        (LinearMap.range
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin) =
      Module.finrank (IntegerRing k) (Fin d → IntegerRing k) :=
  LinearMap.finrank_range_of_inj
    (clearedPowerSeriesMatrix_mulVec_injective (k := k) (d := d) A)

/-! ## Smith normal form of the image lattice -/

/-- The full-rank sublattice generated by the columns of the cleared matrix. -/
def clearedImage
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Submodule (IntegerRing k) (Fin d → IntegerRing k) :=
  LinearMap.range
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin

theorem clearedImage_finrank
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Module.finrank (IntegerRing k) (clearedImage (k := k) (d := d) A) =
      Module.finrank (IntegerRing k) (Fin d → IntegerRing k) := by
  exact clearedPowerSeriesMatrix_range_finrank (k := k) (d := d) A

/-- Smith normal form applied to the construction-owned image lattice.  The
two bases and every diagonal coefficient are produced by the theorem; the
only rank premise is discharged by `clearedImage_finrank`. -/
theorem exists_clearedImage_smith_normal_form
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ∃ (ambientBasis : Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k))
      (diagonalCoeff : Fin d → IntegerRing k)
      (imageBasis : Basis (Fin d) (IntegerRing k)
        (clearedImage (k := k) (d := d) A)),
      ∀ i, (imageBasis i : Fin d → IntegerRing k) =
        diagonalCoeff i • ambientBasis i := by
  exact (clearedImage (k := k) (d := d) A).exists_smith_normal_form_of_rank_eq
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)

/-- The cleared matrix, with codomain restricted to its image, is a linear
equivalence because injectivity has already been proved. -/
def clearedImageEquiv
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (Fin d → IntegerRing k) ≃ₗ[IntegerRing k]
      clearedImage (k := k) (d := d) A :=
  LinearEquiv.ofInjective
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin
    (clearedPowerSeriesMatrix_mulVec_injective (k := k) (d := d) A)

/-- The ambient Smith basis of the standard lattice. -/
def smithAmbientBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k) :=
  (clearedImage (k := k) (d := d) A).smithNormalFormTopBasis
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)

/-- The Smith basis internal to the image lattice. -/
def smithImageBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (clearedImage (k := k) (d := d) A) :=
  (clearedImage (k := k) (d := d) A).smithNormalFormBotBasis
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)

/-- The nonzero diagonal coefficients supplied by Smith normal form. -/
def smithDiagonalCoeff
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : Fin d → IntegerRing k :=
  (clearedImage (k := k) (d := d) A).smithNormalFormCoeffs
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)

theorem smithDiagonalCoeff_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    smithDiagonalCoeff (k := k) (d := d) A i ≠ 0 :=
  (clearedImage (k := k) (d := d) A).smithNormalFormCoeffs_ne_zero
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A) i

/-- Pull the Smith basis of the image back through the cleared matrix.  This
is the domain basis that will become the right integral `GL` factor. -/
def smithDomainBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k) :=
  (smithImageBasis (k := k) (d := d) A).map
    (clearedImageEquiv (k := k) (d := d) A).symm

/-- Coordinate-free Smith diagonalization of the cleared matrix: it maps the
constructed domain basis vector to the corresponding nonzero scalar multiple
of the constructed ambient basis vector. -/
theorem clearedMatrix_apply_smithDomainBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    Matrix.mulVec
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)))
        (smithDomainBasis (k := k) (d := d) A i) =
      smithDiagonalCoeff (k := k) (d := d) A i •
        smithAmbientBasis (k := k) (d := d) A i := by
  change ((clearedImageEquiv (k := k) (d := d) A)
      (smithDomainBasis (k := k) (d := d) A i) :
        Fin d → IntegerRing k) = _
  rw [smithDomainBasis, Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact (clearedImage (k := k) (d := d) A).smithNormalFormBotBasis_def
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A) i

/-- In the two constructed Smith bases, the cleared matrix is diagonal. -/
theorem clearedMatrix_smith_coordinate_matrix
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    LinearMap.toMatrix
        (smithDomainBasis (k := k) (d := d) A)
        (smithAmbientBasis (k := k) (d := d) A)
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin =
      Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) := by
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply]
  change (smithAmbientBasis (k := k) (d := d) A).repr
      (Matrix.mulVec
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)))
        (smithDomainBasis (k := k) (d := d) A j)) i = _
  rw [clearedMatrix_apply_smithDomainBasis (k := k) (d := d) A j]
  by_cases h : i = j <;> simp [h]

/-- The change-of-basis matrix from the standard basis to any basis, bundled
as an actual element of the integral general linear group. -/
def basisChangeGeneralLinear
    {R : Type u} [CommRing R] {d : ℕ}
    (b : Basis (Fin d) R (Fin d → R)) : GL (Fin d) R where
  val := (Pi.basisFun R (Fin d)).toMatrix b
  inv := b.toMatrix (Pi.basisFun R (Fin d))
  val_inv := Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Basis.toMatrix_mul_toMatrix_flip _ _

/-- The left integral change-of-basis factor in Smith diagonalization. -/
def smithAmbientGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  basisChangeGeneralLinear (smithAmbientBasis (k := k) (d := d) A)

/-- The right integral change-of-basis factor in Smith diagonalization. -/
def smithDomainGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  basisChangeGeneralLinear (smithDomainBasis (k := k) (d := d) A)

/-- Matrix-level Smith factorization with both change-of-basis matrices
certified as elements of `GL_d(k[[X]])`. -/
theorem clearedPowerSeriesMatrix_smith_factorization
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (smithAmbientGeneralLinear (k := k) (d := d) A :
          Matrix (Fin d) (Fin d) (IntegerRing k)) *
        Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) *
      (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  symm
  change (Pi.basisFun (IntegerRing k) (Fin d)).toMatrix
        (smithAmbientBasis (k := k) (d := d) A) *
      Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) *
      (smithDomainBasis (k := k) (d := d) A).toMatrix
        (Pi.basisFun (IntegerRing k) (Fin d)) = _
  rw [← clearedMatrix_smith_coordinate_matrix (k := k) (d := d) A]
  calc
    _ = LinearMap.toMatrix
          (Pi.basisFun (IntegerRing k) (Fin d))
          (Pi.basisFun (IntegerRing k) (Fin d))
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin :=
      basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        (Pi.basisFun (IntegerRing k) (Fin d))
        (smithDomainBasis (k := k) (d := d) A)
        (Pi.basisFun (IntegerRing k) (Fin d))
        (smithAmbientBasis (k := k) (d := d) A)
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin
    _ = clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
      rw [LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
        LinearMap.toMatrix'_toLin']

/-! ## Reduction of Smith coefficients to uniformizer powers -/

/-- The exponent of `X` in the DVR factorization of one nonzero Smith
coefficient. -/
def smithExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) : ℕ :=
  Classical.choose
    (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
      (PowerSeries.X_irreducible (R := k)))

/-- The unit multiplying `X ^ smithExponent` in one Smith coefficient. -/
def smithCoeffUnit
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) : (IntegerRing k)ˣ :=
  Classical.choose
    (Classical.choose_spec
      (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
        (PowerSeries.X_irreducible (R := k))))

theorem smithDiagonalCoeff_eq_unit_mul_X_pow
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    smithDiagonalCoeff (k := k) (d := d) A i =
      (smithCoeffUnit (k := k) (d := d) A i : IntegerRing k) *
        PowerSeries.X ^ smithExponent (k := k) (d := d) A i :=
  Classical.choose_spec
    (Classical.choose_spec
      (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
        (PowerSeries.X_irreducible (R := k))))

/-- The diagonal matrix of Smith units is itself an integral general linear
element. -/
def smithUnitGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  diagonalGeneralLinear (IntegerRing k) d
    (smithCoeffUnit (k := k) (d := d) A)

/-- After separating the Smith units, only nonnegative powers of the actual
uniformizer `X` remain on the diagonal. -/
def smithPowerDiagonal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (IntegerRing k) :=
  Matrix.diagonal fun i => PowerSeries.X ^ smithExponent (k := k) (d := d) A i

theorem diagonal_smithDiagonalCoeff_factorization
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) =
      (smithUnitGeneralLinear (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (IntegerRing k)) *
      smithPowerDiagonal (k := k) (d := d) A := by
  change Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) =
    (diagonalGeneralLinear (IntegerRing k) d
        (smithCoeffUnit (k := k) (d := d) A) :
      Matrix (Fin d) (Fin d) (IntegerRing k)) *
    Matrix.diagonal
      (fun i => PowerSeries.X ^ smithExponent (k := k) (d := d) A i)
  rw [show (diagonalGeneralLinear (IntegerRing k) d
      (smithCoeffUnit (k := k) (d := d) A) :
        Matrix (Fin d) (Fin d) (IntegerRing k)) =
      Matrix.diagonal fun i =>
        (smithCoeffUnit (k := k) (d := d) A i : IntegerRing k) by
    apply Matrix.ext
    intro i j
    simp [diagonalGeneralLinear_apply, Matrix.diagonal_apply]]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact smithDiagonalCoeff_eq_unit_mul_X_pow (k := k) (d := d) A i

/-- The Smith ambient basis change with all diagonal units absorbed. -/
def smithLeftGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  smithAmbientGeneralLinear (k := k) (d := d) A *
    smithUnitGeneralLinear (k := k) (d := d) A

/-- Integral Cartan factorization of the cleared matrix with a pure
uniformizer-power diagonal and no residual nonzero scalar assumptions. -/
theorem clearedPowerSeriesMatrix_power_factorization
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (smithLeftGeneralLinear (k := k) (d := d) A :
          Matrix (Fin d) (Fin d) (IntegerRing k)) *
        smithPowerDiagonal (k := k) (d := d) A *
      (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  rw [clearedPowerSeriesMatrix_smith_factorization (k := k) (d := d) A,
    diagonal_smithDiagonalCoeff_factorization (k := k) (d := d) A]
  change _ * (_ * _) * _ = (_ * _) * _ * _
  ac_rfl

/-! ## Passage back to the local field and projective Cartan factors -/

theorem coe_powerSeriesGeneralLinearToLocal
    {k : Type u} [CommRing k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    (powerSeriesGeneralLinearToLocal k d g :
      Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (integerEmbedding k).mapMatrix
        (g : Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  rfl

/-- The pure Smith power diagonal, now invertible over the local field. -/
def smithPowerGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d fun i =>
    uniformizerUnit k ^ smithExponent (k := k) (d := d) A i

theorem map_smithPowerDiagonal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (integerEmbedding k).mapMatrix
        (smithPowerDiagonal (k := k) (d := d) A) =
      (smithPowerGeneralLinearLocal (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, smithPowerDiagonal, Matrix.map_apply,
    smithPowerGeneralLinearLocal, Matrix.diagonal_apply,
    diagonalGeneralLinear_apply]
  by_cases h : i = j
  · subst j
    simp [integerEmbedding, coe_uniformizerUnit,
      HahnSeries.ofPowerSeries_X_pow]
  · simp [h]

/-- The integral left Cartan factor embedded into the local group. -/
def smithLeftGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  powerSeriesGeneralLinearToLocal k d
    (smithLeftGeneralLinear (k := k) (d := d) A)

/-- The integral right Cartan factor embedded into the local group. -/
def smithRightGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  powerSeriesGeneralLinearToLocal k d
    (smithDomainGeneralLinear (k := k) (d := d) A)

theorem map_inv_smithDomainGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (integerEmbedding k).mapMatrix
        (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) =
      ((smithRightGeneralLinearLocal (k := k) (d := d) A)⁻¹ :
        GL (Fin d) (LocalFunctionField k)) := by
  rw [← coe_powerSeriesGeneralLinearToLocal]
  apply congrArg Units.val
  change (powerSeriesGeneralLinearToLocal k d)
      ((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹) =
    ((powerSeriesGeneralLinearToLocal k d)
      (smithDomainGeneralLinear (k := k) (d := d) A))⁻¹
  exact map_inv _ _

/-- The scalar used to clear all denominators, retained as a field unit. -/
def matrixClearingScalarUnit
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Units (LocalFunctionField k) :=
  uniformizerUnit k ^ matrixClearingExponent
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))

/-- Exact local-field Cartan factorization before quotienting the common
denominator-clearing scalar. -/
theorem matrixClearingScalar_mul_eq_localCartanFactors
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.GeneralLinearGroup.scalar (Fin d)
        (matrixClearingScalarUnit (k := k) (d := d) A) * A =
      smithLeftGeneralLinearLocal (k := k) (d := d) A *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
      (smithRightGeneralLinearLocal (k := k) (d := d) A)⁻¹ := by
  apply Units.ext
  change Matrix.scalar (Fin d)
        (matrixClearingScalarUnit (k := k) (d := d) A : LocalFunctionField k) *
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  change (uniformizerUnit k : LocalFunctionField k) ^
      matrixClearingExponent
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) •
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = _
  calc
    _ = (integerEmbedding k).mapMatrix
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) :=
      (map_clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).symm
    _ = (integerEmbedding k).mapMatrix
          ((smithLeftGeneralLinear (k := k) (d := d) A :
              Matrix (Fin d) (Fin d) (IntegerRing k)) *
            smithPowerDiagonal (k := k) (d := d) A *
          (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
              GL (Fin d) (IntegerRing k)) :
                Matrix (Fin d) (Fin d) (IntegerRing k))) :=
      congrArg (integerEmbedding k).mapMatrix
        (clearedPowerSeriesMatrix_power_factorization (k := k) (d := d) A)
    _ = _ := by
      rw [map_mul, map_mul, ← coe_powerSeriesGeneralLinearToLocal,
        map_smithPowerDiagonal (k := k) (d := d) A,
        map_inv_smithDomainGeneralLinear (k := k) (d := d) A]
      rfl

/-- Transport an invertible power-series matrix through the proved
`k[[X]] ≃ 𝒪` equivalence. -/
def powerSeriesGeneralLinearToInteger
    (k : Type u) [Field k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →*
      GL (Fin d) (Valued.integer (LocalFunctionField k)) :=
  Matrix.GeneralLinearGroup.map
    (LocalTopology.powerSeriesIntegerEquiv k).toRingHom

theorem powerSeries_integer_local_triangle
    {k : Type u} [Field k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    integralGeneralLinearToLocal k d
        (powerSeriesGeneralLinearToInteger k d g) =
      powerSeriesGeneralLinearToLocal k d g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Every projectivized power-series `GL` element belongs to the actual
maximal compact subgroup already used by the Haar algebra. -/
theorem mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    {k : Type u} [Field k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    Matrix.ProjGenLinGroup.mk (powerSeriesGeneralLinearToLocal k d g) ∈
      maximalCompact k d := by
  rw [mem_maximalCompact_iff]
  refine ⟨powerSeriesGeneralLinearToInteger k d g, ?_⟩
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d
        (powerSeriesGeneralLinearToInteger k d g)) = _
  rw [powerSeries_integer_local_triangle]

/-- The diagonal projective Cartan representative constructed for one local
general-linear element. -/
def smithPowerCoweight
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk
    (smithPowerGeneralLinearLocal (k := k) (d := d) A)

/-- Projective Cartan equality.  The denominator-clearing scalar disappears
because scalar matrices are killed by `GL_d → PGL_d`. -/
theorem projective_eq_localCartanFactors
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk
          (smithLeftGeneralLinearLocal (k := k) (d := d) A) *
        smithPowerCoweight (k := k) (d := d) A *
      (Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A))⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (matrixClearingScalar_mul_eq_localCartanFactors (k := k) (d := d) A)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    smithPowerCoweight] using h

theorem smithLeft_mem_maximalCompact
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk
        (smithLeftGeneralLinearLocal (k := k) (d := d) A) ∈
      maximalCompact k d :=
  mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    (smithLeftGeneralLinear (k := k) (d := d) A)

theorem smithRight_mem_maximalCompact
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A) ∈
      maximalCompact k d :=
  mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    (smithDomainGeneralLinear (k := k) (d := d) A)

/-- Each projective local element lies in a double coset of the maximal
compact subgroup around an explicitly constructed uniformizer-power
diagonal. -/
theorem mk_mem_smithPower_doubleCoset
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A ∈
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
        ({smithPowerCoweight (k := k) (d := d) A} :
          Set PGL(Fin d, LocalFunctionField k)) *
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
  rw [Set.mem_mul]
  refine ⟨Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A) *
        smithPowerCoweight (k := k) (d := d) A, ?_,
      (Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A))⁻¹, ?_, ?_⟩
  · rw [Set.mem_mul]
    exact ⟨_, smithLeft_mem_maximalCompact (k := k) (d := d) A,
      _, Set.mem_singleton _, rfl⟩
  · exact (maximalCompact k d).inv_mem
      (smithRight_mem_maximalCompact (k := k) (d := d) A)
  · exact (projective_eq_localCartanFactors (k := k) (d := d) A).symm

/-! ## Haar modular character on the Cartan factors -/

/-- The modular character is one on the normalized maximal compact subgroup.
This is proved by evaluating right translation on `K`, whose Haar measure is
exactly one, rather than by assuming continuity of the modular character. -/
theorem modularCharacter_eq_one_of_mem_maximalCompact
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (h : PGL(Fin d, LocalFunctionField k)) (hh : h ∈ maximalCompact k d) :
    MeasureTheory.Measure.modularCharacter h = 1 := by
  let μ := normalizedLocalHaarMeasure k d
  have hmeasure :=
    MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul μ h
  have hK : MeasurableSet
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) :=
    (maximalCompact_isOpen k d).measurableSet
  have heval := congrArg
    (fun ν : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) =>
      ν (maximalCompact k d)) hmeasure
  change (MeasureTheory.Measure.map (fun x => x * h) μ)
      (maximalCompact k d) =
    (MeasureTheory.Measure.modularCharacterFun h • μ)
      (maximalCompact k d) at heval
  rw [MeasureTheory.Measure.map_apply (measurable_mul_const h) hK] at heval
  have hpre :
      (fun x : PGL(Fin d, LocalFunctionField k) => x * h) ⁻¹'
          (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) =
        (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
    ext x
    change x * h ∈ maximalCompact k d ↔ x ∈ maximalCompact k d
    constructor
    · intro hx
      simpa using (maximalCompact k d).mul_mem hx
        ((maximalCompact k d).inv_mem hh)
    · intro hx
      exact (maximalCompact k d).mul_mem hx hh
  dsimp [μ] at heval
  rw [hpre, normalizedLocalHaarMeasure_maximalCompact] at heval
  change MeasureTheory.Measure.modularCharacterFun h = 1
  apply ENNReal.coe_injective
  simpa using heval.symm

/-- The diagonal construction bundled as a monoid homomorphism from tuples
of units. -/
def diagonalGeneralLinearHom (R : Type u) [CommRing R] (d : ℕ) :
    (Fin d → Units R) →* GL (Fin d) R :=
  (Units.map (Matrix.diagonalRingHom (Fin d) R).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

@[simp]
theorem diagonalGeneralLinearHom_apply
    (R : Type u) [CommRing R] (d : ℕ) (v : Fin d → Units R) :
    diagonalGeneralLinearHom R d v = diagonalGeneralLinear R d v :=
  rfl

/-- The tuple with one uniformizer in coordinate `i` and units elsewhere. -/
def coordinateUniformizerUnits
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    Fin d → Units (LocalFunctionField k) :=
  fun j => if j = i then uniformizerUnit k else 1

/-- One-coordinate uniformizer as a local general-linear element. -/
def coordinateUniformizerGeneralLinear
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d
    (coordinateUniformizerUnits k d i)

/-- One-coordinate uniformizer in the projective local group. -/
def coordinateUniformizerCoweight
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk (coordinateUniformizerGeneralLinear k d i)

/-- Multiplying the one-coordinate uniformizers over every coordinate gives
the scalar uniformizer matrix. -/
theorem prod_coordinateUniformizerGeneralLinear
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerGeneralLinear k d)).prod =
      Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k) := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) d
  have htuple :
      ((List.finRange d).map (coordinateUniformizerUnits k d)).prod =
        (fun _ : Fin d => uniformizerUnit k) := by
    funext j
    rw [Pi.list_prod_apply]
    rw [List.map_map]
    change ((List.finRange d).map
      (fun i : Fin d => if j = i then uniformizerUnit k else 1)).prod = _
    rw [← List.ofFn_eq_map, List.prod_ofFn]
    simp
  calc
    ((List.finRange d).map
        (coordinateUniformizerGeneralLinear k d)).prod =
        Φ ((List.finRange d).map
          (coordinateUniformizerUnits k d)).prod := by
      exact List.prod_map_hom (List.finRange d)
        (coordinateUniformizerUnits k d) Φ
    _ = Φ (fun _ : Fin d => uniformizerUnit k) := congrArg Φ htuple
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [Φ, diagonalGeneralLinearHom, Matrix.diagonal_apply]

/-- Consequently, the product of all coordinate coweights is the identity in
the projective group. -/
theorem prod_coordinateUniformizerCoweight
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerCoweight k d)).prod = 1 := by
  calc
    ((List.finRange d).map
        (coordinateUniformizerCoweight k d)).prod =
        Matrix.ProjGenLinGroup.mk
          (((List.finRange d).map
            (coordinateUniformizerGeneralLinear k d)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (coordinateUniformizerGeneralLinear k d)
        Matrix.ProjGenLinGroup.mk
    _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k)) := by
      rw [prod_coordinateUniformizerGeneralLinear]
    _ = 1 := Matrix.ProjGenLinGroup.mk_scalar _

/-- A permutation matrix, bundled as an element of the general linear group. -/
def permutationGeneralLinear
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    GL (Fin d) R where
  val := σ.permMatrix R
  inv := σ⁻¹.permMatrix R
  val_inv := by
    rw [← Matrix.permMatrix_mul]
    simp
  inv_val := by
    rw [← Matrix.permMatrix_mul]
    simp

@[simp]
theorem permutationGeneralLinear_apply
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (i j : Fin d) :
    permutationGeneralLinear R σ i j = σ.permMatrix R i j :=
  rfl

/-- Conjugating a diagonal matrix by a permutation matrix permutes its
diagonal coordinates. -/
theorem permutationGeneralLinear_conj_diagonal
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (v : Fin d → Units R) :
    permutationGeneralLinear R σ * diagonalGeneralLinear R d v *
        (permutationGeneralLinear R σ)⁻¹ =
      diagonalGeneralLinear R d (v ∘ σ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  classical
  simp [permutationGeneralLinear, diagonalGeneralLinear_apply,
    Matrix.mul_apply, Function.comp_def, Equiv.Perm.permMatrix,
    PEquiv.toMatrix]
  rw [Finset.sum_eq_single (σ i)]
  · simp
  · intro b _ hne
    have hib : σ i ≠ b := fun h => hne h.symm
    simp [hib]
  · simp

/-- Any two one-coordinate uniformizers are conjugate by a coordinate
transposition. -/
theorem coordinateUniformizerGeneralLinear_conj
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j) *
        coordinateUniformizerGeneralLinear k d i *
        permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j)⁻¹ =
      coordinateUniformizerGeneralLinear k d j := by
  change
    permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j) *
        diagonalGeneralLinear (LocalFunctionField k) d
          (coordinateUniformizerUnits k d i) *
        (permutationGeneralLinear
          (LocalFunctionField k) (Equiv.swap i j))⁻¹ =
      diagonalGeneralLinear (LocalFunctionField k) d
        (coordinateUniformizerUnits k d j)
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  by_cases hab : a = b
  · subst b
    simp [coordinateUniformizerUnits, diagonalGeneralLinear_apply,
      Function.comp_def, Equiv.swap_apply_eq_iff]
  · simp [hab, diagonalGeneralLinear_apply]

/-- The projective class of a coordinate permutation matrix. -/
def permutationCoweight
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk
    (permutationGeneralLinear (LocalFunctionField k) σ)

/-- Coordinate coweights are conjugate in the projective local group. -/
theorem coordinateUniformizerCoweight_conj
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationCoweight k (Equiv.swap i j) *
        coordinateUniformizerCoweight k d i *
        (permutationCoweight k (Equiv.swap i j))⁻¹ =
      coordinateUniformizerCoweight k d j := by
  exact congrArg Matrix.ProjGenLinGroup.mk
      (coordinateUniformizerGeneralLinear_conj k i j)

/-- Every multiplicative character with commutative codomain is constant on
conjugacy classes.  We record the statement in the exact form needed for the
modular character. -/
theorem monoidHom_conj_eq
    {G M : Type*} [Group G] [CommMonoid M] (χ : G →* M) (x g : G) :
    χ (x * g * x⁻¹) = χ g := by
  calc
    χ (x * g * x⁻¹) = χ x * χ g * χ x⁻¹ := by simp only [map_mul]
    _ = χ g * (χ x * χ x⁻¹) := by ac_rfl
    _ = χ g * χ (x * x⁻¹) := by rw [map_mul]
    _ = χ g := by simp

/-- The modular character takes the same value on every one-coordinate
uniformizer. -/
theorem modularCharacter_coordinateUniformizer_eq
    (k : Type u) [Field k] [Finite k] {d : ℕ} (i j : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) =
      MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d j) := by
  rw [← coordinateUniformizerCoweight_conj k i j]
  exact (monoidHom_conj_eq
    (MeasureTheory.Measure.modularCharacter :
      PGL(Fin d, LocalFunctionField k) →* NNReal)
    (permutationCoweight k (Equiv.swap i j))
    (coordinateUniformizerCoweight k d i)).symm

/-- In positive rank, the modular character is one on every coordinate
uniformizer.  The proof uses all coordinates at once: their projective
product is scalar, while permutation conjugacy makes all character values
equal. -/
theorem modularCharacter_coordinateUniformizer_eq_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) (i : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) = 1 := by
  let δ : PGL(Fin d, LocalFunctionField k) →* NNReal :=
    MeasureTheory.Measure.modularCharacter
  have hprod :
      ((List.finRange d).map
        (fun j => δ (coordinateUniformizerCoweight k d j))).prod = 1 := by
    calc
      ((List.finRange d).map
          (fun j => δ (coordinateUniformizerCoweight k d j))).prod =
          δ (((List.finRange d).map
            (coordinateUniformizerCoweight k d)).prod) := by
        exact List.prod_map_hom (List.finRange d)
          (coordinateUniformizerCoweight k d) δ
      _ = δ 1 := congrArg δ (prod_coordinateUniformizerCoweight k d)
      _ = 1 := map_one δ
  have hconstant :
      (fun j : Fin d => δ (coordinateUniformizerCoweight k d j)) =
        (fun _ : Fin d => δ (coordinateUniformizerCoweight k d i)) := by
    funext j
    exact modularCharacter_coordinateUniformizer_eq k j i
  rw [hconstant] at hprod
  have hpow :
      (δ (coordinateUniformizerCoweight k d i)) ^ d = 1 := by
    simpa using hprod
  exact (pow_eq_one_iff_of_nonneg (by positivity) (Nat.ne_of_gt hd)).mp hpow

/-- The Smith power diagonal is the ordered product of the corresponding
powers of the one-coordinate uniformizers. -/
theorem prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ((List.finRange d).map (fun i =>
        coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerGeneralLinearLocal (k := k) (d := d) A := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) d
  have htuple :
      ((List.finRange d).map (fun i =>
        coordinateUniformizerUnits k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        (fun j => uniformizerUnit k ^
          smithExponent (k := k) (d := d) A j) := by
    funext j
    rw [Pi.list_prod_apply, List.map_map]
    change ((List.finRange d).map (fun i : Fin d =>
      (if j = i then uniformizerUnit k else 1) ^
        smithExponent (k := k) (d := d) A i)).prod = _
    rw [← List.ofFn_eq_map, List.prod_ofFn]
    simp
  calc
    ((List.finRange d).map (fun i =>
        coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        ((List.finRange d).map (fun i =>
          Φ (coordinateUniformizerUnits k d i ^
            smithExponent (k := k) (d := d) A i))).prod := by
      congr 1
      apply List.map_congr_left
      intro i _
      rw [map_pow]
      rfl
    _ = Φ (((List.finRange d).map (fun i =>
          coordinateUniformizerUnits k d i ^
            smithExponent (k := k) (d := d) A i)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerUnits k d i ^
          smithExponent (k := k) (d := d) A i) Φ
    _ = Φ (fun j => uniformizerUnit k ^
          smithExponent (k := k) (d := d) A j) := congrArg Φ htuple
    _ = smithPowerGeneralLinearLocal (k := k) (d := d) A := rfl

/-- Projective form of the coordinate factorization of a Smith power
coweight. -/
theorem prod_coordinateUniformizerCoweight_pow_eq_smithPower
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerCoweight (k := k) (d := d) A := by
  calc
    ((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        ((List.finRange d).map (fun i =>
          Matrix.ProjGenLinGroup.mk
            (coordinateUniformizerGeneralLinear k d i ^
              smithExponent (k := k) (d := d) A i))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      simp [coordinateUniformizerCoweight]
    _ = Matrix.ProjGenLinGroup.mk
        (((List.finRange d).map (fun i =>
          coordinateUniformizerGeneralLinear k d i ^
            smithExponent (k := k) (d := d) A i)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)
        Matrix.ProjGenLinGroup.mk
    _ = smithPowerCoweight (k := k) (d := d) A := by
      rw [prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower]
      rfl

/-- The modular character is one on every Smith power coweight. -/
theorem modularCharacter_smithPowerCoweight_eq_one
    {k : Type u} [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (A : GL (Fin d) (LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter
        (smithPowerCoweight (k := k) (d := d) A) = 1 := by
  let δ : PGL(Fin d, LocalFunctionField k) →* NNReal :=
    MeasureTheory.Measure.modularCharacter
  rw [← prod_coordinateUniformizerCoweight_pow_eq_smithPower A]
  change δ (((List.finRange d).map (fun i =>
    coordinateUniformizerCoweight k d i ^
      smithExponent (k := k) (d := d) A i)).prod) = 1
  calc
    δ (((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod) =
        ((List.finRange d).map (fun i =>
          δ (coordinateUniformizerCoweight k d i ^
            smithExponent (k := k) (d := d) A i))).prod := by
      exact (List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i) δ).symm
    _ = 1 := by
      simp only [map_pow]
      have hone (i : Fin d) :
          δ (coordinateUniformizerCoweight k d i) = 1 :=
        modularCharacter_coordinateUniformizer_eq_one k hd i
      simp_rw [hone]
      simp

/-- The modular character of the projective local group is trivial in every
positive rank.  This is the unimodularity statement needed for Haar
inversion: Cartan decomposition reduces an arbitrary element to two compact
factors and one Smith power coweight. -/
theorem modularCharacter_eq_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (g : PGL(Fin d, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  let left : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A)
  let right : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithRightGeneralLinearLocal (k := k) (d := d) A)
  have hleft :
      MeasureTheory.Measure.modularCharacter left = 1 :=
    modularCharacter_eq_one_of_mem_maximalCompact
      left
      (smithLeft_mem_maximalCompact (k := k) (d := d) A)
  have hright_inv :
      MeasureTheory.Measure.modularCharacter right⁻¹ = 1 :=
    modularCharacter_eq_one_of_mem_maximalCompact
      right⁻¹
      ((maximalCompact k d).inv_mem
        (smithRight_mem_maximalCompact (k := k) (d := d) A))
  have hsmith :
      MeasureTheory.Measure.modularCharacter
        (smithPowerCoweight (k := k) (d := d) A) = 1 :=
    modularCharacter_smithPowerCoweight_eq_one hd A
  rw [projective_eq_localCartanFactors A]
  change MeasureTheory.Measure.modularCharacter
    (left * smithPowerCoweight (k := k) (d := d) A * right⁻¹) = 1
  simp only [map_mul, hleft, hsmith, hright_inv, mul_one]

/-- The two target ranks required by the LSV construction are unimodular. -/
theorem modularCharacter_pgl3_eq_one
    (k : Type u) [Field k] [Finite k]
    (g : PGL(Fin 3, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 :=
  modularCharacter_eq_one k (by decide) g

theorem modularCharacter_pgl4_eq_one
    (k : Type u) [Field k] [Finite k]
    (g : PGL(Fin 4, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 :=
  modularCharacter_eq_one k (by decide) g

/-- Triviality of the modular character makes normalized local Haar measure
right invariant. -/
theorem normalizedLocalHaarMeasure_isMulRightInvariant
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.Measure.IsMulRightInvariant
      (normalizedLocalHaarMeasure k d) := by
  constructor
  intro g
  rw [MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul]
  change (MeasureTheory.Measure.modularCharacter g : NNReal) •
      normalizedLocalHaarMeasure k d = normalizedLocalHaarMeasure k d
  rw [modularCharacter_eq_one k hd g, one_smul]

/-- Normalized local Haar measure is invariant under inversion in positive
rank. -/
theorem normalizedLocalHaarMeasure_isInvInvariant
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) := by
  letI : MeasureTheory.Measure.IsMulRightInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isMulRightInvariant k hd
  constructor
  let μ := normalizedLocalHaarMeasure k d
  let c : ENNReal := MeasureTheory.Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have heval := congrArg
    (fun ν : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) =>
      ν (maximalCompact k d)) hc
  have hc_one : c = 1 := by
    dsimp [μ] at heval
    rw [MeasureTheory.Measure.inv_apply, inv_coe_set,
      normalizedLocalHaarMeasure_maximalCompact] at heval
    simpa using heval.symm
  exact hc.trans (by rw [hc_one, one_smul])

/-! ## The projective contragredient and transpose involutions -/

/-- The contragredient automorphism `A ↦ (A⁻¹)ᵀ` of a general linear
group, constructed on the actual matrices. -/
def contragredientGeneralLinearHom
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    GL n R →* GL n R where
  toFun A :=
    { val := Matrix.transpose (((A⁻¹ : GL n R) : Matrix n n R))
      inv := Matrix.transpose ((A : GL n R) : Matrix n n R)
      val_inv := by
        rw [← Matrix.transpose_mul]
        simp
      inv_val := by
        rw [← Matrix.transpose_mul]
        simp }
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun₂ (Matrix.transpose_one (n := n) (α := R)) i j
  map_mul' A B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change Matrix.transpose
      ((((A * B)⁻¹ : GL n R) : Matrix n n R)) i j = _
    rw [mul_inv_rev]
    exact congrFun₂ (Matrix.transpose_mul
      (((B⁻¹ : GL n R) : Matrix n n R))
      (((A⁻¹ : GL n R) : Matrix n n R))) i j

theorem contragredientGeneralLinear_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : GL n R) :
    contragredientGeneralLinearHom
        (contragredientGeneralLinearHom A) = A := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change Matrix.transpose (Matrix.transpose ((A : Matrix n n R))) i j = _
  rfl

theorem contragredientGeneralLinear_mem_center
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {A : GL n R} (hA : A ∈ Subgroup.center (GL n R)) :
    contragredientGeneralLinearHom A ∈ Subgroup.center (GL n R) := by
  rw [Subgroup.mem_center_iff] at hA ⊢
  intro B
  have h := congrArg contragredientGeneralLinearHom
    (hA (contragredientGeneralLinearHom B))
  simpa only [map_mul, contragredientGeneralLinear_involutive] using h

/-- The contragredient descends through scalar matrices to an actual
automorphism of the projective group. -/
def projectiveContragredientHom
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) →* PGL(n, R) :=
  Matrix.ProjGenLinGroup.lift
    (Matrix.ProjGenLinGroup.mk.comp
      (contragredientGeneralLinearHom (R := R) (n := n))) (by
      ext u
      apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
      apply contragredientGeneralLinear_mem_center
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩)

theorem projectiveContragredient_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) :
    projectiveContragredientHom (projectiveContragredientHom g) = g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A => simp [projectiveContragredientHom,
      contragredientGeneralLinear_involutive]

def projectiveContragredientEquiv
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) ≃* PGL(n, R) where
  toFun := projectiveContragredientHom
  invFun := projectiveContragredientHom
  left_inv := projectiveContragredient_involutive
  right_inv := projectiveContragredient_involutive
  map_mul' := map_mul projectiveContragredientHom

theorem continuous_contragredientGeneralLinear
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (contragredientGeneralLinearHom
      (R := LocalFunctionField k) (n := Fin d)) := by
  apply Units.continuous_iff.2
  exact ⟨(Units.continuous_val.comp continuous_inv).matrix_transpose,
    Units.continuous_val.matrix_transpose⟩

theorem continuous_projectiveContragredient
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (projectiveContragredientHom :
      PGL(Fin d, LocalFunctionField k) →
        PGL(Fin d, LocalFunctionField k)) := by
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (GL (Fin d) (LocalFunctionField k)))).continuous_iff.mpr
  change Continuous (fun A : GL (Fin d) (LocalFunctionField k) ↦
    projectiveContragredientHom (Matrix.ProjGenLinGroup.mk A))
  exact QuotientGroup.continuous_mk.comp
    (continuous_contragredientGeneralLinear (k := k) (d := d))

theorem contragredient_integralGeneralLinearToLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    contragredientGeneralLinearHom (integralGeneralLinearToLocal k d A) =
      integralGeneralLinearToLocal k d
        (contragredientGeneralLinearHom A) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (((integralGeneralLinearToLocal k d A)⁻¹ :
    GL (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (LocalFunctionField k)) j i = _
  rw [← map_inv]
  rfl

theorem projectiveContragredient_mem_maximalCompact
    {k : Type u} [Field k] {d : ℕ}
    {g : PGL(Fin d, LocalFunctionField k)}
    (hg : g ∈ maximalCompact k d) :
    projectiveContragredientHom g ∈ maximalCompact k d := by
  rw [mem_maximalCompact_iff] at hg ⊢
  obtain ⟨A, rfl⟩ := hg
  refine ⟨contragredientGeneralLinearHom A, ?_⟩
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d
        (contragredientGeneralLinearHom A)) =
    projectiveContragredientHom (Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d A))
  rw [← contragredient_integralGeneralLinearToLocal]
  rfl

theorem projectiveContragredient_preimage_maximalCompact
    {k : Type u} [Field k] {d : ℕ} :
    projectiveContragredientHom ⁻¹' (maximalCompact k d :
      Set PGL(Fin d, LocalFunctionField k)) = maximalCompact k d := by
  ext g
  constructor
  · intro hg
    have h := projectiveContragredient_mem_maximalCompact hg
    rw [projectiveContragredient_involutive] at h
    exact h
  · exact projectiveContragredient_mem_maximalCompact

theorem projectiveContragredient_map_normalizedLocalHaarMeasure
    {k : Type u} [Field k] [Finite k] {d : ℕ} :
    MeasureTheory.Measure.map projectiveContragredientHom
        (normalizedLocalHaarMeasure k d) =
      normalizedLocalHaarMeasure k d := by
  let μ := normalizedLocalHaarMeasure k d
  let ν := MeasureTheory.Measure.map projectiveContragredientHom μ
  letI : MeasureTheory.Measure.IsHaarMeasure ν :=
    (projectiveContragredientEquiv :
      PGL(Fin d, LocalFunctionField k) ≃* _).isHaarMeasure_map
        μ continuous_projectiveContragredient
          continuous_projectiveContragredient
  let c : ENNReal := MeasureTheory.Measure.haarScalarFactor ν μ
  have hc : ν = c • μ :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular ν μ
  have heval := congrArg
    (fun m : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) ↦
      m (maximalCompact k d)) hc
  have hν : ν (maximalCompact k d) = 1 := by
    dsimp [ν]
    rw [MeasureTheory.Measure.map_apply
      continuous_projectiveContragredient.measurable
      (maximalCompact_isOpen k d).measurableSet]
    rw [projectiveContragredient_preimage_maximalCompact,
      normalizedLocalHaarMeasure_maximalCompact]
  have hc_one : c = 1 := by
    change ν (maximalCompact k d) =
      (c • μ) (maximalCompact k d) at heval
    rw [hν] at heval
    dsimp [μ] at heval
    rw [normalizedLocalHaarMeasure_maximalCompact] at heval
    simpa using heval.symm
  exact hc.trans (by rw [hc_one, one_smul])

theorem projectiveContragredient_measurePreserving
    {k : Type u} [Field k] [Finite k] {d : ℕ} :
    MeasureTheory.MeasurePreserving projectiveContragredientHom
      (normalizedLocalHaarMeasure k d)
      (normalizedLocalHaarMeasure k d) :=
  ⟨continuous_projectiveContragredient.measurable,
    projectiveContragredient_map_normalizedLocalHaarMeasure⟩

/-- Matrix transpose on `PGL`, expressed as contragredient after inversion.
It is an anti-automorphism rather than a group homomorphism. -/
def projectiveTranspose
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) : PGL(n, R) :=
  projectiveContragredientHom g⁻¹

theorem projectiveTranspose_mul
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g h : PGL(n, R)) :
    projectiveTranspose (g * h) =
      projectiveTranspose h * projectiveTranspose g := by
  simp [projectiveTranspose, mul_inv_rev]

theorem projectiveTranspose_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) : projectiveTranspose (projectiveTranspose g) = g := by
  simp [projectiveTranspose, projectiveContragredient_involutive]

def projectiveTransposeEquiv
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) ≃ PGL(n, R) where
  toFun := projectiveTranspose
  invFun := projectiveTranspose
  left_inv := projectiveTranspose_involutive
  right_inv := projectiveTranspose_involutive

theorem continuous_projectiveTranspose
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (projectiveTranspose :
      PGL(Fin d, LocalFunctionField k) →
        PGL(Fin d, LocalFunctionField k)) :=
  continuous_projectiveContragredient.comp continuous_inv

def projectiveTransposeMeasurableEquiv
    {k : Type u} [Field k] {d : ℕ} :
    PGL(Fin d, LocalFunctionField k) ≃ᵐ
      PGL(Fin d, LocalFunctionField k) where
  toEquiv := projectiveTransposeEquiv
  measurable_toFun := continuous_projectiveTranspose.measurable
  measurable_invFun := continuous_projectiveTranspose.measurable

theorem projectiveTranspose_measurePreserving
    {k : Type u} [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.MeasurePreserving projectiveTranspose
      (normalizedLocalHaarMeasure k d)
      (normalizedLocalHaarMeasure k d) := by
  letI : MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isInvInvariant k hd
  exact projectiveContragredient_measurePreserving.comp
    (MeasureTheory.Measure.measurePreserving_inv
      (normalizedLocalHaarMeasure k d))

/-! ## Dominant Cartan types and their actual double cosets -/

/-- A dominant integral coweight, written in the convention used by the
existing fundamental diagonals: exponents weakly decrease with the matrix
index.  Projectively, two such vectors may still differ by a scalar constant;
that quotient is handled by the uniqueness theorem below rather than hidden
in this structure. -/
structure DominantCoweight (d : ℕ) where
  exponent : Fin d → ℕ
  antitone_exponent : Antitone exponent

@[ext]
theorem DominantCoweight.ext {d : ℕ} {a b : DominantCoweight d}
    (h : a.exponent = b.exponent) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance (d : ℕ) : Countable (DominantCoweight d) :=
  (show Function.Injective DominantCoweight.exponent from
    fun _ _ h => DominantCoweight.ext h).countable

/-- A dominant projective type in positive rank, normalized by requiring its
smallest (last) exponent to be zero.  This is the concrete representative of
the quotient by scalar cocharacters used in `PGL`. -/
structure ProjectiveDominantCoweight (n : ℕ) where
  toDominant : DominantCoweight (n + 1)
  last_exponent_eq_zero : toDominant.exponent (Fin.last n) = 0

@[ext]
theorem ProjectiveDominantCoweight.ext {n : ℕ}
    {a b : ProjectiveDominantCoweight n}
    (h : a.toDominant.exponent = b.toDominant.exponent) : a = b := by
  cases a
  cases b
  cases DominantCoweight.ext h
  rfl

instance (n : ℕ) : Countable (ProjectiveDominantCoweight n) :=
  (show Function.Injective
      (fun weight : ProjectiveDominantCoweight n ↦
        weight.toDominant.exponent) from
    fun _ _ h ↦ ProjectiveDominantCoweight.ext h).countable

/-- Remove the scalar cocharacter from a dominant type by subtracting its
last exponent from every coordinate. -/
def normalizeDominantCoweight {n : ℕ}
    (weight : DominantCoweight (n + 1)) : ProjectiveDominantCoweight n where
  toDominant :=
    { exponent := fun i ↦
        weight.exponent i - weight.exponent (Fin.last n)
      antitone_exponent := by
        intro i j hij
        exact Nat.sub_le_sub_right (weight.antitone_exponent hij) _ }
  last_exponent_eq_zero := Nat.sub_self _

@[simp]
theorem normalizeDominantCoweight_exponent {n : ℕ}
    (weight : DominantCoweight (n + 1)) (i : Fin (n + 1)) :
    (normalizeDominantCoweight weight).toDominant.exponent i =
      weight.exponent i - weight.exponent (Fin.last n) :=
  rfl

/-! ## Entry-order bounds for Cartan uniqueness -/

/-- A uniform lower bound on the Laurent-series orders of all matrix
entries.  This predicate is stable under multiplication and is the basic
determinantal-divisor invariant used below; zero entries have order `⊤`. -/
def MatrixOrderLowerBound {k : Type u} [Field k] {d : ℕ} (m : WithTop ℤ)
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) : Prop :=
  ∀ i j, m ≤ (A i j).orderTop

theorem integralClearingExponent_eq_zero_of_orderTop_nonneg
    {k : Type u} [Field k] (f : LocalFunctionField k)
    (hf : (0 : WithTop ℤ) ≤ f.orderTop) :
    integralClearingExponent f = 0 := by
  by_cases hzero : f = 0
  · simp [hzero, integralClearingExponent]
  · have horder : (0 : ℤ) ≤ f.order := by
      have hf' := hf
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hzero] at hf'
      exact WithTop.coe_le_coe.mp hf'
    rw [integralClearingExponent, Int.toNat_eq_zero]
    exact neg_nonpos.mpr horder

/-- An honestly integral local matrix requires no denominator-clearing
uniformizer power in the constructive Smith reduction. -/
theorem matrixClearingExponent_eq_zero_of_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0 A) :
    matrixClearingExponent A = 0 := by
  classical
  have hentry : ∀ i j,
      integralClearingExponent (A i j) = 0 := by
    intro i j
    exact integralClearingExponent_eq_zero_of_orderTop_nonneg
      (A i j) (hA i j)
  simp [matrixClearingExponent, hentry]

theorem orderTop_finset_sum_lowerBound
    {k : Type u} [Field k]
    {α : Type*} {s : Finset α} {f : α → LocalFunctionField k}
    {m : WithTop ℤ} (h : ∀ a ∈ s, m ≤ (f a).orderTop) :
    m ≤ (∑ a ∈ s, f a).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HahnSeries.orderTop_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (le_min (h a (Finset.mem_insert_self a s))
        (ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb)))).trans
          HahnSeries.min_orderTop_le_orderTop_add

theorem MatrixOrderLowerBound.mul
    {k : Type u} [Field k] {d : ℕ} {a b : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound a A)
    (hB : MatrixOrderLowerBound b B) :
    MatrixOrderLowerBound (a + b) (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  apply orderTop_finset_sum_lowerBound
  intro z _
  rw [HahnSeries.orderTop_mul]
  exact add_le_add (hA i z) (hB z j)

theorem MatrixOrderLowerBound.add
    {k : Type u} [Field k] {d : ℕ} {m : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A)
    (hB : MatrixOrderLowerBound m B) :
    MatrixOrderLowerBound m (A + B) := by
  intro i j
  exact (le_min (hA i j) (hB i j)).trans
    HahnSeries.min_orderTop_le_orderTop_add

/-- Membership in the actual Laurent-series valuation ring is equivalent to
having no negative-order term, in the direction needed for integral matrix
factors. -/
theorem orderTop_nonneg_of_mem_integer
    {k : Type u} [Field k] (x : LocalFunctionField k)
    (hx : x ∈ Valued.integer (LocalFunctionField k)) :
    (0 : WithTop ℤ) ≤ x.orderTop := by
  rw [Valuation.mem_integer_iff] at hx
  obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe k x).1 hx
  rw [← hF, HahnSeries.zero_le_orderTop_iff]
  by_contra hnonneg
  have hneg : (F : LocalFunctionField k).order < 0 := lt_of_not_ge hnonneg
  have hcoeff :
      (F : LocalFunctionField k).coeff (F : LocalFunctionField k).order = 0 := by
    rw [PowerSeries.coeff_coe]
    simp [hneg]
  have hzero : (F : LocalFunctionField k) = 0 :=
    HahnSeries.coeff_order_eq_zero.mp hcoeff
  rw [hzero, HahnSeries.order_zero] at hneg
  exact (lt_irrefl 0 hneg)

theorem integralGeneralLinearToLocal_orderLowerBound
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    MatrixOrderLowerBound 0
      (integralGeneralLinearToLocal k d A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  intro i j
  apply orderTop_nonneg_of_mem_integer
  exact (A i j).property

theorem integralGeneralLinearToLocal_inv_orderLowerBound
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    MatrixOrderLowerBound 0
      (((integralGeneralLinearToLocal k d A)⁻¹ :
          GL (Fin d) (LocalFunctionField k)) :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  simpa only [map_inv] using
    (integralGeneralLinearToLocal_orderLowerBound (k := k) (A := A⁻¹))

/-- Equality in the projective general linear group is equality upstairs up
to an actual scalar matrix. -/
theorem exists_scalar_mul_eq_of_projective_mk_eq
    {R : Type u} [Field R] {d : ℕ}
    {A B : GL (Fin d) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    ∃ c : Units R,
      A = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
  have hcenter : A * B⁻¹ ∈ Subgroup.center (GL (Fin d) R) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    rw [map_mul, map_inv, h]
    simp
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  refine ⟨c, ?_⟩
  calc
    A = (A * B⁻¹) * B := by simp
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by rw [← hc]

/-- Additive Laurent order of a nonzero local-field unit. -/
def localUnitOrder {k : Type u} [Field k]
    (c : Units (LocalFunctionField k)) : ℤ :=
  (c : LocalFunctionField k).order

theorem orderTop_coe_localUnit
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    (c : LocalFunctionField k).orderTop =
      (localUnitOrder c : WithTop ℤ) := by
  exact (HahnSeries.order_eq_orderTop_of_ne_zero c.ne_zero).symm

theorem scalarGeneralLinear_orderLowerBound
    {k : Type u} [Field k] {d : ℕ}
    (c : Units (LocalFunctionField k)) :
    MatrixOrderLowerBound (localUnitOrder c : WithTop ℤ)
      (Matrix.GeneralLinearGroup.scalar (Fin d) c :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [orderTop_coe_localUnit]
  · simp [hij,
      HahnSeries.orderTop_zero]

@[simp]
theorem orderTop_uniformizerUnit_pow
    {k : Type u} [Field k] (m : ℕ) :
    ((uniformizerUnit k ^ m : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop = (m : WithTop ℤ) := by
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (by simp)]
  simp [coe_uniformizerUnit]

@[simp]
theorem localUnitOrder_uniformizerUnit_pow
    {k : Type u} [Field k] (m : ℕ) :
    localUnitOrder (uniformizerUnit k ^ m) = (m : ℤ) := by
  have h := orderTop_uniformizerUnit_pow (k := k) m
  rw [orderTop_coe_localUnit] at h
  exact WithTop.coe_eq_coe.mp h

theorem localUnitOrder_inv
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    localUnitOrder c⁻¹ = -localUnitOrder c := by
  have hmul := HahnSeries.order_mul c.ne_zero c⁻¹.ne_zero
  have hprod :
      (c : LocalFunctionField k) * (c⁻¹ : Units (LocalFunctionField k)) = 1 := by
    simp
  rw [hprod, HahnSeries.order_one] at hmul
  apply eq_neg_of_add_eq_zero_left
  simpa [localUnitOrder, add_comm] using hmul.symm

theorem localUnitOrder_mul
    {k : Type u} [Field k]
    (a b : Units (LocalFunctionField k)) :
    localUnitOrder (a * b) = localUnitOrder a + localUnitOrder b := by
  exact HahnSeries.order_mul a.ne_zero b.ne_zero

theorem localUnitOrder_pow
    {k : Type u} [Field k]
    (a : Units (LocalFunctionField k)) (m : ℕ) :
    localUnitOrder (a ^ m) = m * localUnitOrder a := by
  induction m with
  | zero => simp [localUnitOrder]
  | succ m ih =>
      rw [pow_succ, localUnitOrder_mul, ih]
      push_cast
      ring

theorem localUnitOrder_prod
    {k : Type u} [Field k] {α : Type*}
    (s : Finset α) (f : α → Units (LocalFunctionField k)) :
    localUnitOrder (∏ i ∈ s, f i) =
      ∑ i ∈ s, localUnitOrder (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localUnitOrder]
  | @insert a s ha ih =>
      simp [ha, localUnitOrder_mul, ih]

theorem orderTop_coe_localUnit_inv
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop =
      ((-localUnitOrder c : ℤ) : WithTop ℤ) := by
  rw [orderTop_coe_localUnit, localUnitOrder_inv]

theorem localUnitOrder_eq_zero_of_mem_integer_and_inv
    {k : Type u} [Field k]
    (c : Units (LocalFunctionField k))
    (hc : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k))
    (hcinv : ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k) ∈ Valued.integer (LocalFunctionField k)) :
    localUnitOrder c = 0 := by
  have hcOrder := orderTop_nonneg_of_mem_integer (c : LocalFunctionField k) hc
  have hcinvOrder := orderTop_nonneg_of_mem_integer
    (((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k)) hcinv
  rw [orderTop_coe_localUnit] at hcOrder
  rw [orderTop_coe_localUnit_inv] at hcinvOrder
  have hcInt := WithTop.coe_le_coe.mp hcOrder
  have hcinvInt := WithTop.coe_le_coe.mp hcinvOrder
  omega

theorem integralGeneralLinear_det_localUnitOrder_eq_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A)) = 0 := by
  let c := Matrix.GeneralLinearGroup.det
    (integralGeneralLinearToLocal k d A)
  have hc : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have hdet : Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A) =
      Units.map (SubringClass.subtype
        (Valued.integer (LocalFunctionField k)))
        (Matrix.GeneralLinearGroup.det A) :=
      Matrix.GeneralLinearGroup.map_det
        (SubringClass.subtype (Valued.integer (LocalFunctionField k))) A
    change ((Matrix.GeneralLinearGroup.det
      (integralGeneralLinearToLocal k d A) :
        Units (LocalFunctionField k)) : LocalFunctionField k) ∈ _
    rw [hdet]
    exact (Matrix.GeneralLinearGroup.det A).val.property
  have hcinv : ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k) ∈ Valued.integer (LocalFunctionField k) := by
    have hdetInv : c⁻¹ = Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A⁻¹) := by
      dsimp [c]
      simp
    have hmapInv : Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A⁻¹) =
      Units.map (SubringClass.subtype
        (Valued.integer (LocalFunctionField k)))
        (Matrix.GeneralLinearGroup.det A⁻¹) :=
      Matrix.GeneralLinearGroup.map_det
        (SubringClass.subtype (Valued.integer (LocalFunctionField k))) A⁻¹
    rw [hdetInv, hmapInv]
    exact (Matrix.GeneralLinearGroup.det A⁻¹).val.property
  exact localUnitOrder_eq_zero_of_mem_integer_and_inv c hc hcinv

/-- The determinant of an invertible power-series matrix remains a local
unit after embedding in the Laurent-series field. -/
theorem powerSeriesGeneralLinear_det_localUnitOrder_eq_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (IntegerRing k)) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (powerSeriesGeneralLinearToLocal k d A)) = 0 := by
  rw [← powerSeries_integer_local_triangle]
  exact integralGeneralLinear_det_localUnitOrder_eq_zero
    (powerSeriesGeneralLinearToInteger k d A)

/-- The determinant order of the Smith power diagonal is the sum of its
Smith exponents. -/
theorem smithPowerGeneralLinearLocal_det_localUnitOrder
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (smithPowerGeneralLinearLocal (k := k) (d := d) A)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by
  have hdet : Matrix.GeneralLinearGroup.det
      (smithPowerGeneralLinearLocal (k := k) (d := d) A) =
      ∏ i, uniformizerUnit k ^ smithExponent (k := k) (d := d) A i := by
    apply Units.ext
    simp [smithPowerGeneralLinearLocal, diagonalGeneralLinear,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdet, localUnitOrder_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact localUnitOrder_uniformizerUnit_pow _

/-- For an invertible local matrix whose entries are integral, the sum of
the constructive Smith exponents is exactly the local order of its
determinant.  No denominator-clearing shift remains. -/
theorem smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) :
    (∑ i, (smithExponent (k := k) (d := d) A i : ℤ)) =
      localUnitOrder (Matrix.GeneralLinearGroup.det A) := by
  have hclear : matrixClearingExponent
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = 0 :=
    matrixClearingExponent_eq_zero_of_orderLowerBound_zero _ hA
  have hdet := congrArg Matrix.GeneralLinearGroup.det
    (matrixClearingScalar_mul_eq_localCartanFactors
      (k := k) (d := d) A)
  have horder := congrArg localUnitOrder hdet
  simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    matrixClearingScalarUnit, hclear, localUnitOrder_mul,
    localUnitOrder_inv,
    smithLeftGeneralLinearLocal, smithRightGeneralLinearLocal,
    powerSeriesGeneralLinear_det_localUnitOrder_eq_zero,
    smithPowerGeneralLinearLocal_det_localUnitOrder] using horder.symm

/-- Sort a finite exponent tuple into the dominant (weakly decreasing)
order. -/
def dominantSortPermutation {d : ℕ} (n : Fin d → ℕ) :
    Equiv.Perm (Fin d) :=
  Tuple.sort (OrderDual.toDual ∘ n)

/-- The sorted exponent tuple. -/
def dominantSort {d : ℕ} (n : Fin d → ℕ) : Fin d → ℕ :=
  n ∘ dominantSortPermutation n

theorem dominantSort_antitone {d : ℕ} (n : Fin d → ℕ) :
    Antitone (dominantSort n) := by
  intro i j hij
  exact Tuple.monotone_sort (OrderDual.toDual ∘ n) hij

/-- The dominant type produced by the constructive Smith reduction. -/
def smithDominantCoweight
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : DominantCoweight d where
  exponent := dominantSort (smithExponent (k := k) (d := d) A)
  antitone_exponent := dominantSort_antitone _

/-- Sorting the Smith exponents into dominant order preserves their sum. -/
theorem smithDominantCoweight_exponent_sum
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (∑ i, ((smithDominantCoweight A).exponent i : ℤ)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by
  simpa [smithDominantCoweight, dominantSort, Function.comp_def] using
    (Equiv.sum_comp
      (dominantSortPermutation
        (smithExponent (k := k) (d := d) A))
      (fun i => (smithExponent (k := k) (d := d) A i : ℤ)))

/-- The actual local diagonal attached to a dominant coweight. -/
def dominantGeneralLinear
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d fun i =>
    uniformizerUnit k ^ weight.exponent i

/-- Projective representative of a dominant coweight. -/
def dominantCoweight
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k weight)

/-- Projective transpose fixes every dominant diagonal representative. -/
theorem projectiveTranspose_dominantCoweight
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    projectiveTranspose (dominantCoweight k weight) =
      dominantCoweight k weight := by
  change Matrix.ProjGenLinGroup.mk
      (contragredientGeneralLinearHom
        (dominantGeneralLinear k weight)⁻¹) =
    Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k weight)
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change Matrix.transpose
    ((dominantGeneralLinear k weight :
      Matrix (Fin d) (Fin d) (LocalFunctionField k))) i j = _
  by_cases h : i = j
  · subst j
    rfl
  · simp [dominantGeneralLinear, diagonalGeneralLinear_apply, h, ne_comm]

/-- The Cartan double coset `K a_λ K` attached to a dominant type. -/
def dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    Set PGL(Fin d, LocalFunctionField k) :=
  (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
    ({dominantCoweight k weight} : Set PGL(Fin d, LocalFunctionField k)) *
    (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k))

/-- Restoring the removed last exponent is multiplication by a scalar
matrix. -/
theorem scalar_mul_normalizedDominantGeneralLinear
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
        (uniformizerUnit k ^ weight.exponent (Fin.last n)) *
      dominantGeneralLinear k (normalizeDominantCoweight weight).toDominant =
        dominantGeneralLinear k weight := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) (n + 1)
  have hscalar_base :
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k) =
        Φ (fun _ : Fin (n + 1) ↦ uniformizerUnit k) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Φ, diagonalGeneralLinearHom, Matrix.diagonal_apply]
  have hscalar :
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k ^ weight.exponent (Fin.last n)) =
        Φ (fun _ : Fin (n + 1) ↦
          uniformizerUnit k ^ weight.exponent (Fin.last n)) := by
    calc
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k ^ weight.exponent (Fin.last n)) =
          (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
            (uniformizerUnit k)) ^ weight.exponent (Fin.last n) := by
            rw [map_pow]
      _ = (Φ (fun _ : Fin (n + 1) ↦ uniformizerUnit k)) ^
          weight.exponent (Fin.last n) := by rw [hscalar_base]
      _ = Φ ((fun _ : Fin (n + 1) ↦ uniformizerUnit k) ^
          weight.exponent (Fin.last n)) := by rw [map_pow]
      _ = Φ (fun _ : Fin (n + 1) ↦
          uniformizerUnit k ^ weight.exponent (Fin.last n)) := by
            congr 1
  rw [hscalar]
  change Φ (fun _ : Fin (n + 1) ↦
      uniformizerUnit k ^ weight.exponent (Fin.last n)) *
    Φ (fun i ↦ uniformizerUnit k ^
      (weight.exponent i - weight.exponent (Fin.last n))) =
    Φ (fun i ↦ uniformizerUnit k ^ weight.exponent i)
  rw [← map_mul]
  congr 1
  funext i
  have hlast : weight.exponent (Fin.last n) ≤ weight.exponent i :=
    weight.antitone_exponent (Fin.le_last i)
  change uniformizerUnit k ^ weight.exponent (Fin.last n) *
      uniformizerUnit k ^
        (weight.exponent i - weight.exponent (Fin.last n)) =
    uniformizerUnit k ^ weight.exponent i
  rw [← pow_add, Nat.add_comm,
    Nat.sub_add_cancel hlast]

/-- Normalization does not change the projective diagonal because the
discarded common uniformizer power is scalar. -/
theorem dominantCoweight_normalize
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    dominantCoweight k (normalizeDominantCoweight weight).toDominant =
      dominantCoweight k weight := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_normalizedDominantGeneralLinear k weight)
  simpa only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    dominantCoweight] using h

/-- The projectively normalized Cartan double coset. -/
def projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    Set PGL(Fin (n + 1), LocalFunctionField k) :=
  dominantDoubleCoset k weight.toDominant

theorem dominantDoubleCoset_normalize
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    dominantDoubleCoset k (normalizeDominantCoweight weight).toDominant =
      dominantDoubleCoset k weight := by
  simp only [dominantDoubleCoset, dominantCoweight_normalize]

theorem dominantGeneralLinear_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (weight : DominantCoweight d) :
    MatrixOrderLowerBound 0
      (dominantGeneralLinear k weight :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  intro i j
  rw [dominantGeneralLinear, diagonalGeneralLinear_apply]
  split
  · simp
  · simp [HahnSeries.orderTop_zero]

theorem projectiveDominant_last_entry_order
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    ((dominantGeneralLinear k weight.toDominant :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k))
        (Fin.last n) (Fin.last n)).orderTop = 0 := by
  simp [dominantGeneralLinear, weight.last_exponent_eq_zero]

theorem dominantGeneralLinear_det_localUnitOrder
    {k : Type u} [Field k] {d : ℕ}
    (weight : DominantCoweight d) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (dominantGeneralLinear k weight)) =
      ∑ i, (weight.exponent i : ℤ) := by
  have hdet : Matrix.GeneralLinearGroup.det
      (dominantGeneralLinear k weight) =
      ∏ i, uniformizerUnit k ^ weight.exponent i := by
    apply Units.ext
    simp [dominantGeneralLinear, diagonalGeneralLinear,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdet, localUnitOrder_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact localUnitOrder_uniformizerUnit_pow _

@[simp]
theorem orderTop_uniformizerUnit_pow_inv
    {k : Type u} [Field k] (m : ℕ) :
    (((uniformizerUnit k ^ m)⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop =
      ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
  rw [orderTop_coe_localUnit_inv]
  have h := orderTop_uniformizerUnit_pow (k := k) m
  rw [orderTop_coe_localUnit] at h
  have hInt : localUnitOrder (uniformizerUnit k ^ m) = (m : ℤ) :=
    WithTop.coe_eq_coe.mp h
  rw [hInt]

theorem projectiveDominant_inv_orderLowerBound_first
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    MatrixOrderLowerBound
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      (((dominantGeneralLinear k weight.toDominant)⁻¹ :
          GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
  change MatrixOrderLowerBound _
    (diagonalGeneralLinear (LocalFunctionField k) (n + 1)
      (fun i ↦ (uniformizerUnit k ^
        weight.toDominant.exponent i)⁻¹) :
      Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k))
  intro i j
  rw [diagonalGeneralLinear_apply]
  split
  · subst j
    rw [orderTop_uniformizerUnit_pow_inv]
    exact WithTop.coe_le_coe.mpr (neg_le_neg
      (Int.ofNat_le.mpr
        (weight.toDominant.antitone_exponent (Fin.zero_le i))))
  · simp [HahnSeries.orderTop_zero]

theorem projectiveDominant_inv_first_entry_order
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin (n + 1)) (LocalFunctionField k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) 0 0).orderTop =
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ) := by
  change (((uniformizerUnit k ^
    weight.toDominant.exponent (0 : Fin (n + 1)))⁻¹ :
      Units (LocalFunctionField k)) : LocalFunctionField k).orderTop = _
  exact orderTop_uniformizerUnit_pow_inv _

theorem dominantCoweight_mem_doubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    dominantCoweight k weight ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset, Set.mem_mul]
  refine ⟨dominantCoweight k weight, ?_, 1, (maximalCompact k d).one_mem,
    mul_one _⟩
  rw [Set.mem_mul]
  exact ⟨1, (maximalCompact k d).one_mem, dominantCoweight k weight,
    Set.mem_singleton _, one_mul _⟩

theorem dominantDoubleCoset_isCompact
    (k : Type u) [Field k] [Finite k] {d : ℕ}
    (weight : DominantCoweight d) : IsCompact (dominantDoubleCoset k weight) := by
  exact ((maximalCompact_isCompact k d).mul isCompact_singleton).mul
    (maximalCompact_isCompact k d)

theorem dominantDoubleCoset_isOpen
    (k : Type u) [Field k] [Finite k] {d : ℕ}
    (weight : DominantCoweight d) : IsOpen (dominantDoubleCoset k weight) := by
  exact ((maximalCompact_isOpen k d).mul_right).mul_right

theorem dominantDoubleCoset_measurableSet
    (k : Type u) [Field k] [Finite k] {d : ℕ}
    (weight : DominantCoweight d) : MeasurableSet (dominantDoubleCoset k weight) :=
  (dominantDoubleCoset_isOpen k weight).measurableSet

/-- The existing `r`-th fundamental diagonal is the dominant type with one
in the first `r` coordinates and zero elsewhere. -/
def fundamentalDominantCoweight (d r : ℕ) : DominantCoweight d where
  exponent i := if i.val < r then 1 else 0
  antitone_exponent := by
    intro i j hij
    by_cases hj : j.val < r
    · have hi : i.val < r := lt_of_le_of_lt (Fin.mk_le_mk.mp hij) hj
      simp [hi, hj]
    · simp [hj]

/-- A nonnegative dominant coweight in positive dimension whose coordinates
sum to one is the first fundamental coweight. -/
theorem dominantCoweight_eq_fundamental_one_of_sum_eq_one
    {d : ℕ} (hd : 0 < d) (weight : DominantCoweight d)
    (hsum : ∑ i, weight.exponent i = 1) :
    weight = fundamentalDominantCoweight d 1 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hterm_le_one (i : Fin d) : weight.exponent i ≤ 1 := by
    calc
      weight.exponent i ≤ ∑ j, weight.exponent j := by
        exact Finset.single_le_sum
          (fun j _ => Nat.zero_le (weight.exponent j))
          (Finset.mem_univ i)
      _ = 1 := hsum
  have hfirst_ne_zero : weight.exponent (0 : Fin d) ≠ 0 := by
    intro hzero
    have hall : ∀ i, weight.exponent i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero
        (hzero ▸ weight.antitone_exponent (Fin.zero_le i))
    have hsumZero : ∑ i, weight.exponent i = 0 := by
      simp [hall]
    omega
  have hfirst : weight.exponent (0 : Fin d) = 1 := by
    have hle := hterm_le_one (0 : Fin d)
    omega
  apply DominantCoweight.ext
  funext i
  simp only [fundamentalDominantCoweight]
  split_ifs with hi
  · have hiZero : i = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    simpa [hiZero] using hfirst
  · have hiNeZero : i ≠ 0 := by
      intro hiZero
      subst i
      simp at hi
    by_contra hnonzero
    have hiPos : 1 ≤ weight.exponent i :=
      Nat.one_le_iff_ne_zero.mpr hnonzero
    have hzeroMem : (0 : Fin d) ∈ Finset.univ.erase i := by
      simp [hiNeZero.symm]
    have hzeroLe : weight.exponent (0 : Fin d) ≤
        ∑ j ∈ Finset.univ.erase i, weight.exponent j := by
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le (weight.exponent j)) hzeroMem
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset (Fin d)) weight.exponent (Finset.mem_univ i)
    rw [hsum] at hsplit
    omega

theorem dominantGeneralLinear_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantGeneralLinear k (fundamentalDominantCoweight d r) =
      fundamentalDiagonal k d r := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [dominantGeneralLinear, fundamentalDominantCoweight,
    fundamentalDiagonal, fundamentalDiagonalUnits,
    diagonalGeneralLinear_apply]

theorem dominantCoweight_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantCoweight k (fundamentalDominantCoweight d r) =
      fundamentalCoweight k d r := by
  exact congrArg Matrix.ProjGenLinGroup.mk
    (dominantGeneralLinear_fundamental k d r)

theorem dominantDoubleCoset_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantDoubleCoset k (fundamentalDominantCoweight d r) =
      fundamentalDoubleCoset k d r := by
  simp [dominantDoubleCoset, fundamentalDoubleCoset,
    dominantCoweight_fundamental]

/-- A permutation matrix over the power-series ring maps to the same
permutation matrix over the local field. -/
theorem powerSeriesGeneralLinearToLocal_permutation
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    powerSeriesGeneralLinearToLocal k d
        (permutationGeneralLinear (IntegerRing k) σ) =
      permutationGeneralLinear (LocalFunctionField k) σ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [powerSeriesGeneralLinearToLocal, permutationGeneralLinear,
    Matrix.GeneralLinearGroup.map_apply, integerEmbedding,
    Equiv.Perm.permMatrix, PEquiv.toMatrix]

/-- Every coordinate permutation is represented by an element of the actual
maximal compact subgroup. -/
theorem permutationCoweight_mem_maximalCompact
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permutationCoweight k σ ∈ maximalCompact k d := by
  rw [permutationCoweight,
    ← powerSeriesGeneralLinearToLocal_permutation k σ]
  exact mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    (permutationGeneralLinear (IntegerRing k) σ)

/-- Sorting the Smith exponents is implemented by conjugation with an actual
permutation matrix. -/
theorem permutation_conj_smithPower_eq_dominant
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
        (permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantGeneralLinear k (smithDominantCoweight A) := by
  change
    permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        diagonalGeneralLinear (LocalFunctionField k) d
          (fun i => uniformizerUnit k ^
            smithExponent (k := k) (d := d) A i) *
        (permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      diagonalGeneralLinear (LocalFunctionField k) d
        (fun i => uniformizerUnit k ^
          dominantSort (smithExponent (k := k) (d := d) A) i)
  rw [permutationGeneralLinear_conj_diagonal]
  rfl

theorem permutation_conj_smithPowerCoweight_eq_dominant
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerCoweight (k := k) (d := d) A *
        (permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantCoweight k (smithDominantCoweight A) := by
  simpa [permutationCoweight, smithPowerCoweight, dominantCoweight] using
    congrArg Matrix.ProjGenLinGroup.mk
      (permutation_conj_smithPower_eq_dominant A)

/-- Constructive Cartan coverage by dominant double cosets. -/
theorem mk_mem_dominantDoubleCoset
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A ∈
      dominantDoubleCoset k (smithDominantCoweight A) := by
  let left : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A)
  let right : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithRightGeneralLinearLocal (k := k) (d := d) A)
  let perm : PGL(Fin d, LocalFunctionField k) :=
    permutationCoweight k
      (dominantSortPermutation (smithExponent (k := k) (d := d) A))
  let diagonal : PGL(Fin d, LocalFunctionField k) :=
    smithPowerCoweight (k := k) (d := d) A
  let dominant : PGL(Fin d, LocalFunctionField k) :=
    dominantCoweight k (smithDominantCoweight A)
  have hleft : left ∈ maximalCompact k d :=
    smithLeft_mem_maximalCompact A
  have hright : right ∈ maximalCompact k d :=
    smithRight_mem_maximalCompact A
  have hperm : perm ∈ maximalCompact k d :=
    permutationCoweight_mem_maximalCompact k _
  have hconj : perm * diagonal * perm⁻¹ = dominant :=
    permutation_conj_smithPowerCoweight_eq_dominant A
  have hfactor :
      Matrix.ProjGenLinGroup.mk A =
        (left * perm⁻¹) * dominant * (perm * right⁻¹) := by
    rw [← hconj]
    rw [projective_eq_localCartanFactors A]
    simp [left, right, diagonal, mul_assoc]
  rw [dominantDoubleCoset, Set.mem_mul]
  refine ⟨(left * perm⁻¹) * dominant, ?_, perm * right⁻¹,
    (maximalCompact k d).mul_mem hperm
      ((maximalCompact k d).inv_mem hright), hfactor.symm⟩
  rw [Set.mem_mul]
  exact ⟨left * perm⁻¹,
    (maximalCompact k d).mul_mem hleft
      ((maximalCompact k d).inv_mem hperm),
    dominant, Set.mem_singleton _, rfl⟩

/-- Every projective local element has a dominant Cartan representative. -/
theorem exists_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ}
    (g : PGL(Fin d, LocalFunctionField k)) :
    ∃ weight : DominantCoweight d, g ∈ dominantDoubleCoset k weight := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  exact ⟨smithDominantCoweight A, mk_mem_dominantDoubleCoset A⟩

/-- The dominant Cartan double cosets form a countable compact cover. -/
theorem iUnion_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} :
    ⋃ weight : DominantCoweight d, dominantDoubleCoset k weight = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨weight, hg⟩ := exists_mem_dominantDoubleCoset k g
  exact Set.mem_iUnion.2 ⟨weight, hg⟩

/-- Every positive-rank projective local element lies in a double coset
indexed by a scalar-normalized dominant type. -/
theorem exists_mem_projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (g : PGL(Fin (n + 1), LocalFunctionField k)) :
    ∃ weight : ProjectiveDominantCoweight n,
      g ∈ projectiveDominantDoubleCoset k weight := by
  obtain ⟨weight, hg⟩ := exists_mem_dominantDoubleCoset k g
  refine ⟨normalizeDominantCoweight weight, ?_⟩
  rw [projectiveDominantDoubleCoset,
    dominantDoubleCoset_normalize]
  exact hg

/-- The normalized projective Cartan double cosets give the required
countable compact cover in every positive rank, in particular ranks three
and four. -/
theorem iUnion_projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ} :
    ⋃ weight : ProjectiveDominantCoweight n,
      projectiveDominantDoubleCoset k weight = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨weight, hg⟩ :=
    exists_mem_projectiveDominantDoubleCoset k g
  exact Set.mem_iUnion.2 ⟨weight, hg⟩

theorem projectiveDominantDoubleCoset_isCompact
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    IsCompact (projectiveDominantDoubleCoset k weight) :=
  dominantDoubleCoset_isCompact k weight.toDominant

theorem projectiveDominantDoubleCoset_isOpen
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    IsOpen (projectiveDominantDoubleCoset k weight) :=
  dominantDoubleCoset_isOpen k weight.toDominant

theorem projectiveDominantDoubleCoset_measurableSet
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    MeasurableSet (projectiveDominantDoubleCoset k weight) :=
  (projectiveDominantDoubleCoset_isOpen k weight).measurableSet

/-- The existing fundamental color `r` is already scalar-normalized whenever
`1 ≤ r ≤ n` in rank `n+1`. -/
def fundamentalProjectiveDominantCoweight
    (n r : ℕ) (hr : r ≤ n) : ProjectiveDominantCoweight n where
  toDominant := fundamentalDominantCoweight (n + 1) r
  last_exponent_eq_zero := by
    simp [fundamentalDominantCoweight, hr]

theorem projectiveDominantDoubleCoset_fundamental
    (k : Type u) [Field k] (n r : ℕ) (hr : r ≤ n) :
    projectiveDominantDoubleCoset k
        (fundamentalProjectiveDominantCoweight n r hr) =
      fundamentalDoubleCoset k (n + 1) r := by
  exact dominantDoubleCoset_fundamental k (n + 1) r

theorem left_mul_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ dominantDoubleCoset k weight) :
    h * x ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, z, hz, rfl⟩
  rcases hy with ⟨a, ha, b, hb, rfl⟩
  refine ⟨(h * a) * b, ?_, z, hz, ?_⟩
  · exact ⟨h * a, (maximalCompact k d).mul_mem hh ha,
      b, hb, rfl⟩
  · simp [mul_assoc]

theorem right_mul_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ dominantDoubleCoset k weight) :
    x * h ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, z, hz, rfl⟩
  exact ⟨y, hy, z * h, (maximalCompact k d).mul_mem hz hh,
    by simp [mul_assoc]⟩

theorem left_mul_mem_dominantDoubleCoset_iff
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d) :
    h * x ∈ dominantDoubleCoset k weight ↔
      x ∈ dominantDoubleCoset k weight := by
  constructor
  · intro hx
    have hx' := left_mul_mem_dominantDoubleCoset k weight
      ((maximalCompact k d).inv_mem hh) hx
    simpa using hx'
  · exact left_mul_mem_dominantDoubleCoset k weight hh

theorem right_mul_mem_dominantDoubleCoset_iff
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d) :
    x * h ∈ dominantDoubleCoset k weight ↔
      x ∈ dominantDoubleCoset k weight := by
  constructor
  · intro hx
    have hx' := right_mul_mem_dominantDoubleCoset k weight
      ((maximalCompact k d).inv_mem hh) hx
    simpa using hx'
  · exact right_mul_mem_dominantDoubleCoset k weight hh

theorem projectiveTranspose_mem_maximalCompact
    (k : Type u) [Field k] {d : ℕ}
    {g : PGL(Fin d, LocalFunctionField k)}
    (hg : g ∈ maximalCompact k d) :
    projectiveTranspose g ∈ maximalCompact k d :=
  projectiveContragredient_mem_maximalCompact
    ((maximalCompact k d).inv_mem hg)

/-- Matrix transpose preserves every dominant Cartan double coset. -/
theorem projectiveTranspose_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {x : PGL(Fin d, LocalFunctionField k)}
    (hx : x ∈ dominantDoubleCoset k weight) :
    projectiveTranspose x ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, right, hright, rfl⟩
  rcases hy with ⟨left, hleft, diagonal, hdiagonal, rfl⟩
  have hdiag : diagonal = dominantCoweight k weight :=
    Set.mem_singleton_iff.mp hdiagonal
  subst diagonal
  refine ⟨projectiveTranspose right * dominantCoweight k weight, ?_,
    projectiveTranspose left, projectiveTranspose_mem_maximalCompact k hleft,
    ?_⟩
  · exact ⟨projectiveTranspose right,
      projectiveTranspose_mem_maximalCompact k hright,
      dominantCoweight k weight, Set.mem_singleton _, rfl⟩
  · rw [projectiveTranspose_mul, projectiveTranspose_mul,
      projectiveTranspose_dominantCoweight]
    simp [mul_assoc]

theorem projectiveTranspose_mem_dominantDoubleCoset_iff
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    (x : PGL(Fin d, LocalFunctionField k)) :
    projectiveTranspose x ∈ dominantDoubleCoset k weight ↔
      x ∈ dominantDoubleCoset k weight := by
  constructor
  · intro hx
    have h := projectiveTranspose_mem_dominantDoubleCoset k weight hx
    simpa only [projectiveTranspose_involutive] using h
  · exact projectiveTranspose_mem_dominantDoubleCoset k weight

/-- If two Cartan double cosets meet, the diagonal representative of either
one lies in the other. -/
theorem dominantCoweight_mem_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {d : ℕ}
    (a b : DominantCoweight d)
    (hinter : (dominantDoubleCoset k a ∩
      dominantDoubleCoset k b).Nonempty) :
    dominantCoweight k a ∈ dominantDoubleCoset k b := by
  obtain ⟨x, hxa, hxb⟩ := hinter
  rw [dominantDoubleCoset] at hxa
  rcases hxa with ⟨y, hy, right, hright, rfl⟩
  rcases hy with ⟨left, hleft, diagonal, hdiagonal, rfl⟩
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  have hleft' := left_mul_mem_dominantDoubleCoset k b
    ((maximalCompact k d).inv_mem hleft) hxb
  have hright' := right_mul_mem_dominantDoubleCoset k b
    ((maximalCompact k d).inv_mem hright) hleft'
  simpa [mul_assoc] using hright'

/-- Once both dominant types are scalar-normalized, the scalar appearing
when a projective double-coset equality is lifted to `GL` has Laurent order
zero. -/
theorem scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    ∃ (left right :
        GL (Fin (n + 1)) (Valued.integer (LocalFunctionField k)))
      (c : Units (LocalFunctionField k)),
      localUnitOrder c = 0 ∧
      dominantGeneralLinear k a.toDominant =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c *
          (integralGeneralLinearToLocal k (n + 1) left *
            dominantGeneralLinear k b.toDominant *
            integralGeneralLinearToLocal k (n + 1) right) := by
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset] at hmem
  rcases hmem with ⟨y, hy, rightP, hrightP, hproduct⟩
  rcases hy with ⟨leftP, hleftP, diagonal, hdiagonal, hyproduct⟩
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  change leftP ∈ maximalCompact k (n + 1) at hleftP
  change rightP ∈ maximalCompact k (n + 1) at hrightP
  rw [mem_maximalCompact_iff] at hleftP hrightP
  obtain ⟨left, hleft⟩ := hleftP
  obtain ⟨right, hright⟩ := hrightP
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) left) = leftP at hleft
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) right) = rightP at hright
  have hprojective :
      Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k a.toDominant) =
        Matrix.ProjGenLinGroup.mk
          (integralGeneralLinearToLocal k (n + 1) left *
            dominantGeneralLinear k b.toDominant *
            integralGeneralLinearToLocal k (n + 1) right) := by
    change dominantCoweight k a.toDominant = _
    rw [map_mul, map_mul, hleft, hright]
    rw [← hyproduct] at hproduct
    exact hproduct.symm
  obtain ⟨c, hGL⟩ :=
    exists_scalar_mul_eq_of_projective_mk_eq hprojective
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hleftBound : MatrixOrderLowerBound 0
      (leftLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound left
  have hrightBound : MatrixOrderLowerBound 0
      (rightLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound right
  have hdiagonalABound : MatrixOrderLowerBound 0
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero a.toDominant
  have hdiagonalBBound : MatrixOrderLowerBound 0
      (diagonalB : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero b.toDominant
  have hscalarBound : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (scalar : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    scalarGeneralLinear_orderLowerBound c
  have hrightProductBound : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (scalar * (leftLocal * diagonalB * rightLocal) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using hscalarBound.mul
      ((hleftBound.mul hdiagonalBBound).mul hrightBound)
  have hmatrix :
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) =
      (scalar * (leftLocal * diagonalB * rightLocal) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    congrArg Units.val hGL
  have hdiagonalALowerC : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) := by
    rw [hmatrix]
    exact hrightProductBound
  have hc_le : localUnitOrder c ≤ 0 := by
    have h := hdiagonalALowerC (Fin.last n) (Fin.last n)
    rw [projectiveDominant_last_entry_order a] at h
    exact WithTop.coe_le_coe.mp h
  have hleftInvBound : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hrightInvBound : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hscalarInvBound : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      ((scalar⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [show scalar⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c⁻¹ by
        exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv] using
      (scalarGeneralLinear_orderLowerBound (d := n + 1) c⁻¹)
  have hreverse :
      diagonalB = leftLocal⁻¹ * scalar⁻¹ * diagonalA * rightLocal⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hreverseProductBound : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      (leftLocal⁻¹ * scalar⁻¹ * diagonalA * rightLocal⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using
      (((hleftInvBound.mul hscalarInvBound).mul hdiagonalABound).mul
        hrightInvBound)
  have hdiagonalBLowerNegC : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      (diagonalB : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) := by
    rw [hreverse]
    exact hreverseProductBound
  have hnegc_le : -localUnitOrder c ≤ 0 := by
    have h := hdiagonalBLowerNegC (Fin.last n) (Fin.last n)
    rw [projectiveDominant_last_entry_order b] at h
    exact WithTop.coe_le_coe.mp h
  refine ⟨left, right, c, ?_, hGL⟩
  omega

/-- The largest normalized Cartan exponent cannot increase when its
representative is placed in another normalized Cartan double coset. -/
theorem projectiveDominant_first_exponent_le_of_mem_doubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    a.toDominant.exponent (0 : Fin (n + 1)) ≤
      b.toDominant.exponent (0 : Fin (n + 1)) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hdiagonalBInv :=
    projectiveDominant_inv_orderLowerBound_first (k := k) b
  have hscalarInv : MatrixOrderLowerBound 0
      ((scalar⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [show scalar⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c⁻¹ by
        exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv, hc] using
      (scalarGeneralLinear_orderLowerBound (d := n + 1) c⁻¹)
  have hinverse :
      diagonalA⁻¹ =
        rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hproduct : MatrixOrderLowerBound
      ((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      (rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using
      (((hrightInv.mul hdiagonalBInv).mul hleftInv).mul hscalarInv)
  have hboundA : MatrixOrderLowerBound
      ((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      ((diagonalA⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [hinverse]
    exact hproduct
  have hentry := hboundA (0 : Fin (n + 1)) 0
  rw [projectiveDominant_inv_first_entry_order a] at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  omega

theorem projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a.toDominant.exponent (0 : Fin (n + 1)) =
      b.toDominant.exponent (0 : Fin (n + 1)) := by
  have hab : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k a.toDominant b.toDominant
    exact hinter
  have hba : dominantCoweight k b.toDominant ∈
      projectiveDominantDoubleCoset k a := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k b.toDominant a.toDominant
    exact ⟨hinter.choose, hinter.choose_spec.2, hinter.choose_spec.1⟩
  exact le_antisymm
    (projectiveDominant_first_exponent_le_of_mem_doubleCoset k a b hab)
    (projectiveDominant_first_exponent_le_of_mem_doubleCoset k b a hba)

/-- The determinant recovers the sum of the normalized Cartan exponents;
integral left/right factors and the projective scalar all have order zero. -/
theorem projectiveDominant_exponent_sum_eq_of_mem_doubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  have hdet := congrArg Matrix.GeneralLinearGroup.det hGL
  have horder := congrArg localUnitOrder hdet
  simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    localUnitOrder_mul, localUnitOrder_pow, hc,
    integralGeneralLinear_det_localUnitOrder_eq_zero,
    dominantGeneralLinear_det_localUnitOrder] using horder

theorem projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by
  apply projectiveDominant_exponent_sum_eq_of_mem_doubleCoset k a b
  apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
    k a.toDominant b.toDominant
  exact hinter

/-- Full uniqueness of the normalized dominant Cartan type in rank three. -/
theorem projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 2)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a = b := by
  have hfirst :=
    projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have hsum :=
    projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have halast : a.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using a.last_exponent_eq_zero
  have hblast : b.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using b.last_exponent_eq_zero
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i
  · exact hfirst
  · simp [Fin.sum_univ_succ, halast, hblast] at hsum
    change a.toDominant.exponent (1 : Fin 3) =
      b.toDominant.exponent (1 : Fin 3)
    omega
  · exact halast.trans hblast.symm

theorem projectiveDominantDoubleCoset_rankThree_disjoint
    (k : Type u) [Field k]
    {a b : ProjectiveDominantCoweight 2} (hab : a ≠ b) :
    Disjoint (projectiveDominantDoubleCoset k a)
      (projectiveDominantDoubleCoset k b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
    k a b ⟨x, hxa, hxb⟩)

@[simp]
theorem diagonalGeneralLinear_inv
    (R : Type u) [CommRing R] (d : ℕ) (v : Fin d → Units R) :
    (diagonalGeneralLinear R d v)⁻¹ =
      diagonalGeneralLinear R d (fun i => (v i)⁻¹) := by
  change (diagonalGeneralLinearHom R d v)⁻¹ =
    diagonalGeneralLinearHom R d (fun i => (v i)⁻¹)
  rw [← map_inv]
  rfl

/-! ### The second compound matrix in rank four -/

/-- First coordinate of the lexicographically ordered two-subsets of
`Fin 4`: `01, 02, 03, 12, 13, 23`. -/
def rankFourWedgeFirst : Fin 6 → Fin 4 :=
  ![0, 0, 0, 1, 1, 2]

/-- Second coordinate of the lexicographically ordered two-subsets of
`Fin 4`: `01, 02, 03, 12, 13, 23`. -/
def rankFourWedgeSecond : Fin 6 → Fin 4 :=
  ![1, 2, 3, 2, 3, 3]

/-- The concrete matrix of second exterior minors for a `4 × 4` matrix. -/
def rankFourSecondCompound
    {R : Type u} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 6) (Fin 6) R :=
  fun p q ↦
    A (rankFourWedgeFirst p) (rankFourWedgeFirst q) *
        A (rankFourWedgeSecond p) (rankFourWedgeSecond q) -
      A (rankFourWedgeFirst p) (rankFourWedgeSecond q) *
        A (rankFourWedgeSecond p) (rankFourWedgeFirst q)

@[simp]
theorem rankFourSecondCompound_one
    {R : Type u} [CommRing R] :
    rankFourSecondCompound (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [rankFourSecondCompound, rankFourWedgeFirst,
      rankFourWedgeSecond, Matrix.one_apply]

/-- Cauchy--Binet for the six explicit second exterior minors. -/
theorem rankFourSecondCompound_mul
    {R : Type u} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) :
    rankFourSecondCompound (A * B) =
      rankFourSecondCompound A * rankFourSecondCompound B := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [rankFourSecondCompound, rankFourWedgeFirst,
      rankFourWedgeSecond, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- The second compound of an invertible rank-four matrix, bundled as an
actual invertible `6 × 6` matrix. -/
def rankFourSecondCompoundGeneralLinear
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) : GL (Fin 6) R where
  val := rankFourSecondCompound A
  inv := rankFourSecondCompound
    (((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R))
  val_inv := by
    rw [← rankFourSecondCompound_mul]
    simp
  inv_val := by
    rw [← rankFourSecondCompound_mul]
    simp

@[simp]
theorem rankFourSecondCompoundGeneralLinear_inv_val
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) :
    (((rankFourSecondCompoundGeneralLinear A)⁻¹ : GL (Fin 6) R) :
      Matrix (Fin 6) (Fin 6) R) =
      rankFourSecondCompound
        (((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R)) := by
  change (rankFourSecondCompoundGeneralLinear A).inv =
    rankFourSecondCompound A.inv
  rfl

theorem rankFourSecondCompoundGeneralLinear_mul
    {R : Type u} [CommRing R] (A B : GL (Fin 4) R) :
    rankFourSecondCompoundGeneralLinear (A * B) =
      rankFourSecondCompoundGeneralLinear A *
        rankFourSecondCompoundGeneralLinear B := by
  apply Matrix.GeneralLinearGroup.ext
  exact congrFun₂ (rankFourSecondCompound_mul
    (A : Matrix (Fin 4) (Fin 4) R) B)

theorem rankFourSecondCompoundGeneralLinear_inv
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) :
    rankFourSecondCompoundGeneralLinear A⁻¹ =
      (rankFourSecondCompoundGeneralLinear A)⁻¹ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congrFun₂
    (rankFourSecondCompoundGeneralLinear_inv_val A).symm i j

theorem rankFourSecondCompound_orderLowerBound
    {k : Type u} [Field k] {m : WithTop ℤ}
    {A : Matrix (Fin 4) (Fin 4) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A) :
    MatrixOrderLowerBound (m + m) (rankFourSecondCompound A) := by
  intro p q
  apply (le_min ?_ ?_).trans
    HahnSeries.min_orderTop_le_orderTop_sub
  · rw [HahnSeries.orderTop_mul]
    exact add_le_add (hA _ _) (hA _ _)
  · rw [HahnSeries.orderTop_mul]
    exact add_le_add (hA _ _) (hA _ _)

theorem rankFourSecondCompound_diagonal
    {R : Type u} [CommRing R] (v : Fin 4 → R) :
    rankFourSecondCompound (Matrix.diagonal v) =
      Matrix.diagonal (fun p ↦
        v (rankFourWedgeFirst p) * v (rankFourWedgeSecond p)) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [rankFourSecondCompound, rankFourWedgeFirst,
      rankFourWedgeSecond]

theorem projectiveDominant_rankFour_wedgePair_sum_le_first
    (weight : ProjectiveDominantCoweight 3) (p : Fin 6) :
    weight.toDominant.exponent (rankFourWedgeFirst p) +
        weight.toDominant.exponent (rankFourWedgeSecond p) ≤
      weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) := by
  have h01 := weight.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := weight.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := weight.toDominant.antitone_exponent
    (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases p <;>
    simp [rankFourWedgeFirst, rankFourWedgeSecond] <;>
    omega

theorem projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
    {k : Type u} [Field k]
    (weight : ProjectiveDominantCoweight 3) :
    MatrixOrderLowerBound
      ((-((weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear
          (dominantGeneralLinear k weight.toDominant))⁻¹ :
          GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
  rw [rankFourSecondCompoundGeneralLinear_inv_val]
  change MatrixOrderLowerBound _ (rankFourSecondCompound
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))))
  have hdiagInv := congrArg Units.val
    (diagonalGeneralLinear_inv (LocalFunctionField k) 4
      (fun i ↦ uniformizerUnit k ^ weight.toDominant.exponent i))
  change ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))) = _ at hdiagInv
  rw [hdiagInv]
  have hdiagVal :
      (diagonalGeneralLinear (LocalFunctionField k) 4
        (fun i ↦ (uniformizerUnit k ^
          weight.toDominant.exponent i)⁻¹) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) =
      Matrix.diagonal (fun i ↦
        (((uniformizerUnit k ^ weight.toDominant.exponent i)⁻¹ :
          Units (LocalFunctionField k)) : LocalFunctionField k)) := by
    apply Matrix.ext
    intro i j
    simp only [diagonalGeneralLinear_apply, Matrix.diagonal_apply]
  rw [hdiagVal, rankFourSecondCompound_diagonal]
  intro p q
  rw [Matrix.diagonal_apply]
  split
  · subst q
    rw [HahnSeries.orderTop_mul,
      orderTop_uniformizerUnit_pow_inv,
      orderTop_uniformizerUnit_pow_inv]
    apply WithTop.coe_le_coe.mpr
    push_cast
    have hp := projectiveDominant_rankFour_wedgePair_sum_le_first weight p
    omega
  · simp [HahnSeries.orderTop_zero]

theorem projectiveDominant_rankFour_secondCompound_inv_first_entry_order
    {k : Type u} [Field k]
    (weight : ProjectiveDominantCoweight 3) :
    (((((rankFourSecondCompoundGeneralLinear
        (dominantGeneralLinear k weight.toDominant))⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
      Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) 0 0).orderTop) =
      ((-((weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) := by
  rw [rankFourSecondCompoundGeneralLinear_inv_val]
  change (rankFourSecondCompound
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))) 0 0).orderTop = _
  have hdiagInv := congrArg Units.val
    (diagonalGeneralLinear_inv (LocalFunctionField k) 4
      (fun i ↦ uniformizerUnit k ^ weight.toDominant.exponent i))
  change ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))) = _ at hdiagInv
  rw [hdiagInv]
  have hdiagVal :
      (diagonalGeneralLinear (LocalFunctionField k) 4
        (fun i ↦ (uniformizerUnit k ^
          weight.toDominant.exponent i)⁻¹) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) =
      Matrix.diagonal (fun i ↦
        (((uniformizerUnit k ^ weight.toDominant.exponent i)⁻¹ :
          Units (LocalFunctionField k)) : LocalFunctionField k)) := by
    apply Matrix.ext
    intro i j
    simp only [diagonalGeneralLinear_apply, Matrix.diagonal_apply]
  rw [hdiagVal, rankFourSecondCompound_diagonal]
  change ((((uniformizerUnit k ^ weight.toDominant.exponent (0 : Fin 4))⁻¹ :
      Units (LocalFunctionField k)) : LocalFunctionField k) *
    (((uniformizerUnit k ^ weight.toDominant.exponent (1 : Fin 4))⁻¹ :
      Units (LocalFunctionField k)) : LocalFunctionField k)).orderTop = _
  rw [HahnSeries.orderTop_mul,
    orderTop_uniformizerUnit_pow_inv,
    orderTop_uniformizerUnit_pow_inv]
  push_cast
  simp [add_comm]

/-- The sum of the two largest normalized Cartan exponents cannot increase
when a rank-four representative is placed in another normalized Cartan
double coset.  This is the first-entry valuation argument applied to the
second exterior-power representation. -/
theorem projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) ≤
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  let leftLocal := integralGeneralLinearToLocal k 4 left
  let rightLocal := integralGeneralLinearToLocal k 4 right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin 4) c
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hscalarInv : MatrixOrderLowerBound 0
      ((scalar⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) := by
    rw [show scalar⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 4) c⁻¹ by
      exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv, hc] using
      (scalarGeneralLinear_orderLowerBound (d := 4) c⁻¹)
  have hrightCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hrightInv
  have hleftCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hleftInv
  have hscalarCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear scalar)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hscalarInv
  have hdiagonalBCompoundInv :=
    projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
      (k := k) b
  have hinverse :
      diagonalA⁻¹ =
        rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hcompoundInverse :
      (rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ =
        (rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalar)⁻¹ := by
    have h := congrArg rankFourSecondCompoundGeneralLinear hinverse
    rw [rankFourSecondCompoundGeneralLinear_inv] at h
    rw [rankFourSecondCompoundGeneralLinear_mul,
      rankFourSecondCompoundGeneralLinear_mul,
      rankFourSecondCompoundGeneralLinear_mul] at h
    rw [rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv] at h
    exact h
  have hproduct : MatrixOrderLowerBound
      ((-((b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalar)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    simpa only [zero_add, add_zero, Units.val_mul, diagonalB] using
      (((hrightCompoundInv.mul hdiagonalBCompoundInv).mul
        hleftCompoundInv).mul hscalarCompoundInv)
  have hboundA : MatrixOrderLowerBound
      ((-((b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [hcompoundInverse]
    exact hproduct
  have hentry := hboundA (0 : Fin 6) 0
  dsimp [diagonalA] at hentry
  rw [projectiveDominant_rankFour_secondCompound_inv_first_entry_order a]
    at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  push_cast at hint
  omega

theorem projectiveDominant_rankFour_firstTwoSum_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) =
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) := by
  have hab : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b := by
    exact dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k a.toDominant b.toDominant hinter
  have hba : dominantCoweight k b.toDominant ∈
      projectiveDominantDoubleCoset k a := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k b.toDominant a.toDominant
    rw [Set.inter_comm]
    exact hinter
  exact le_antisymm
    (projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
      k a b hab)
    (projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
      k b a hba)

/-- Full uniqueness of the normalized dominant Cartan type in rank four. -/
theorem projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a = b := by
  have hfirst :=
    projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have hfirstTwo :=
    projectiveDominant_rankFour_firstTwoSum_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have hsum :=
    projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have halast : a.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using a.last_exponent_eq_zero
  have hblast : b.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using b.last_exponent_eq_zero
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i
  · exact hfirst
  · change a.toDominant.exponent (1 : Fin 4) =
      b.toDominant.exponent (1 : Fin 4)
    omega
  · simp [Fin.sum_univ_succ, halast, hblast] at hsum
    change a.toDominant.exponent (2 : Fin 4) =
      b.toDominant.exponent (2 : Fin 4)
    omega
  · exact halast.trans hblast.symm

theorem projectiveDominantDoubleCoset_rankFour_disjoint
    (k : Type u) [Field k]
    {a b : ProjectiveDominantCoweight 3} (hab : a ≠ b) :
    Disjoint (projectiveDominantDoubleCoset k a)
      (projectiveDominantDoubleCoset k b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
    k a b ⟨x, hxa, hxb⟩)

/-! ## Inversion of the fundamental rank-three and rank-four coweights -/

theorem scalar_mul_fundamentalDiagonal_rankThree_one_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (uniformizerUnit k) *
        (fundamentalDiagonal k 3 1)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 3 2 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 3
      (fundamentalDiagonalUnits k 3 2) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]

theorem scalar_mul_fundamentalDiagonal_rankThree_two_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (uniformizerUnit k) *
        (fundamentalDiagonal k 3 2)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 3 1 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 3
      (fundamentalDiagonalUnits k 3 1) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]

theorem scalar_mul_fundamentalDiagonal_rankFour_one_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 4) (uniformizerUnit k) *
        (fundamentalDiagonal k 4 1)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 4 3 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 4
      (fundamentalDiagonalUnits k 4 3) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]

theorem scalar_mul_fundamentalDiagonal_rankFour_two_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 4) (uniformizerUnit k) *
        (fundamentalDiagonal k 4 2)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 4 2 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 4
      (fundamentalDiagonalUnits k 4 2) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]

theorem scalar_mul_fundamentalDiagonal_rankFour_three_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 4) (uniformizerUnit k) *
        (fundamentalDiagonal k 4 3)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 4 1 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 4
      (fundamentalDiagonalUnits k 4 1) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]

/-- In `PGL₃`, inversion exchanges the two fundamental coweights, up to
conjugation by the longest coordinate permutation. -/
theorem fundamentalCoweight_rankThree_one_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 3 1)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 3 2 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_fundamentalDiagonal_rankThree_one_inv k)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    fundamentalCoweight, permutationCoweight] using h

theorem fundamentalCoweight_rankThree_two_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 3 2)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 3 1 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_fundamentalDiagonal_rankThree_two_inv k)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    fundamentalCoweight, permutationCoweight] using h

/-- In `PGL₄`, inversion exchanges colors one and three. -/
theorem fundamentalCoweight_rankFour_one_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 4 1)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 4 3 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_fundamentalDiagonal_rankFour_one_inv k)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    fundamentalCoweight, permutationCoweight] using h

/-- The middle fundamental coweight of `PGL₄` is self-dual, up to conjugation
by the longest coordinate permutation. -/
theorem fundamentalCoweight_rankFour_two_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 4 2)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 4 2 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_fundamentalDiagonal_rankFour_two_inv k)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    fundamentalCoweight, permutationCoweight] using h

theorem fundamentalCoweight_rankFour_three_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 4 3)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 4 1 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (scalar_mul_fundamentalDiagonal_rankFour_three_inv k)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    fundamentalCoweight, permutationCoweight] using h

/-- Conjugating the middle representative by an element of a subgroup does
not change its double coset. -/
theorem subgroup_doubleCoset_conj
    {G : Type*} [Group G] (K : Subgroup G) {b p : G} (hp : p ∈ K) :
    (K : Set G) * {p * b * p⁻¹} * (K : Set G) =
      (K : Set G) * {b} * (K : Set G) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, ⟨l, hl, c, hc, rfl⟩, r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨(l * p) * b, ?_, p⁻¹ * r,
      K.mul_mem (K.inv_mem hp) hr, ?_⟩
    · exact ⟨l * p, K.mul_mem hl hp, b, Set.mem_singleton b, rfl⟩
    · simp only [mul_assoc]
  · intro hx
    rcases hx with ⟨y, ⟨l, hl, c, hc, rfl⟩, r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨(l * p⁻¹) * (p * b * p⁻¹), ?_, p * r,
      K.mul_mem hp hr, ?_⟩
    · exact ⟨l * p⁻¹, K.mul_mem hl (K.inv_mem hp),
        p * b * p⁻¹, Set.mem_singleton _, rfl⟩
    · simp only [mul_assoc, inv_mul_cancel_left]

/-- Inverting a subgroup double coset replaces its representative by its
inverse; a conjugating subgroup element is absorbed on the two sides. -/
theorem subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    {G : Type*} [Group G] (K : Subgroup G) {a b p : G}
    (hp : p ∈ K) (hab : a⁻¹ = p * b * p⁻¹) :
    ((K : Set G) * {a} * (K : Set G))⁻¹ =
      (K : Set G) * {b} * (K : Set G) := by
  have hKinv : ((K : Set G))⁻¹ = (K : Set G) := by
    ext x
    simp
  calc
    ((K : Set G) * {a} * (K : Set G))⁻¹ =
        (K : Set G) * {a⁻¹} * (K : Set G) := by
      simp only [mul_inv_rev, Set.inv_singleton, hKinv, mul_assoc]
    _ = (K : Set G) * {p * b * p⁻¹} * (K : Set G) := by rw [hab]
    _ = (K : Set G) * {b} * (K : Set G) :=
      subgroup_doubleCoset_conj K hp

theorem fundamentalDoubleCoset_rankThree_one_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 3 1)⁻¹ =
      fundamentalDoubleCoset k 3 2 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 3)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankThree_one_inv k)

theorem fundamentalDoubleCoset_rankThree_two_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 3 2)⁻¹ =
      fundamentalDoubleCoset k 3 1 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 3)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankThree_two_inv k)

theorem fundamentalDoubleCoset_rankFour_one_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 4 1)⁻¹ =
      fundamentalDoubleCoset k 4 3 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 4)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankFour_one_inv k)

theorem fundamentalDoubleCoset_rankFour_two_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 4 2)⁻¹ =
      fundamentalDoubleCoset k 4 2 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 4)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankFour_two_inv k)

theorem fundamentalDoubleCoset_rankFour_three_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 4 3)⁻¹ =
      fundamentalDoubleCoset k 4 1 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 4)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankFour_three_inv k)

end QEC.Coding.HighDimensionalExpander.SphericalHecke
