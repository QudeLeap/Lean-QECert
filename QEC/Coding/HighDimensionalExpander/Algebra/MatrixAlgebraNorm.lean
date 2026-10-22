import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing

/-!
# The algebra norm of a matrix algebra

The ordinary algebra norm of `M_n(R)` is the determinant of left
multiplication on the `n²`-dimensional matrix algebra.  This file identifies
it with the `n`-th power of the usual matrix determinant.  The distinction is
needed when comparing an intrinsic regular norm with reduced norms obtained
from different splittings of a central simple algebra.
-/

open scoped Matrix

namespace Polynomial

/-- A polynomial with constant coefficient one has at most one normalized
`n`-th root when `n` is nonzero in the coefficient domain.  The normalization
removes the usual root-of-unity ambiguity: in the factorization of
`f ^ n - g ^ n`, the complementary factor has constant coefficient `n`. -/
theorem eq_of_pow_eq_pow_of_coeff_zero_eq_one
    {R : Type*} [CommRing R]
    {f g : R[X]} {n : ℕ}
    (hn : IsUnit (n : R))
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1)
    (hpow : f ^ n = g ^ n) :
    f = g := by
  let s : R[X] := ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hproduct : (f - g) * s = 0 := by
    rw [show (f - g) * s = f ^ n - g ^ n by
      exact (Commute.all f g).mul_geom_sum₂ n]
    rw [hpow, sub_self]
  have hfe : f.eval 0 = 1 := by
    simpa [coeff_zero_eq_eval_zero] using hf
  have hge : g.eval 0 = 1 := by
    simpa [coeff_zero_eq_eval_zero] using hg
  have hscoeff : s.coeff 0 = (n : R) := by
    rw [coeff_zero_eq_eval_zero]
    rw [show s = ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i) by rfl,
      eval_finsetSum]
    simp [hfe, hge]
  apply sub_eq_zero.mp
  apply eq_zero_of_mul_eq_zero_of_smul s
  · intro a ha
    have hacoeff := congrArg (fun p : R[X] ↦ p.coeff 0) ha
    change (a • s).coeff 0 = (0 : R[X]).coeff 0 at hacoeff
    rw [coeff_smul, hscoeff, coeff_zero] at hacoeff
    exact hn.mul_right_cancel (by simpa [smul_eq_mul] using hacoeff)
  · simpa [mul_comm] using hproduct

end Polynomial

namespace Matrix

open scoped Polynomial

/-- The determinant along the affine line from the identity matrix to `A`.
Its constant coefficient is one, which removes the root-of-unity ambiguity
when comparing powers of reduced norms. -/
noncomputable def affineLineDet
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : R[X] :=
  Matrix.det ((1 : Matrix n n R[X]) +
    (Polynomial.X : R[X]) •
      (A.map (Polynomial.C : R →+* R[X]) - 1))

theorem eval_affineLineDet
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (a : R) :
    Polynomial.eval a (affineLineDet A) =
      Matrix.det ((1 : Matrix n n R) + a • (A - 1)) := by
  rw [affineLineDet]
  change Polynomial.evalRingHom a
    (Matrix.det ((1 : Matrix n n R[X]) +
      (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval a
      ((if i = j then 1 else 0) + Polynomial.X *
        (Polynomial.C (A i j) - (if i = j then 1 else 0))) =
    (if i = j then 1 else 0) + a *
      (A i j - (if i = j then 1 else 0))
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem affineLineDet_coeff_zero
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    (affineLineDet A).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_affineLineDet]
  rw [zero_smul, add_zero, Matrix.det_one]

theorem affineLineDet_eval_one
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Polynomial.eval 1 (affineLineDet A) = Matrix.det A := by
  rw [eval_affineLineDet]
  congr 1
  module

theorem map_affineLineDet
    {R S n : Type*} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (A : Matrix n n R) :
    Polynomial.map f (affineLineDet A) = affineLineDet (A.map f) := by
  change Polynomial.mapRingHom f (Matrix.det
      ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) = _
  rw [RingHom.map_det]
  change Matrix.det ((Polynomial.mapRingHom f).mapMatrix
      ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) =
    Matrix.det ((1 : Matrix n n S[X]) + (Polynomial.X : S[X]) •
      ((A.map f).map (Polynomial.C : S →+* S[X]) - 1))
  apply congrArg (fun M : Matrix n n S[X] => Matrix.det M)
  apply Matrix.ext
  intro i j
  change Polynomial.map f
      ((if i = j then 1 else 0) + Polynomial.X *
        (Polynomial.C (A i j) - (if i = j then 1 else 0))) =
    (if i = j then 1 else 0) + Polynomial.X *
      (Polynomial.C (f (A i j)) - (if i = j then 1 else 0))
  by_cases hij : i = j <;> simp [hij]

/-- The normalized affine-line determinant is invariant under conjugation by
a matrix with a supplied right inverse. -/
theorem affineLineDet_conj
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A Z Zi : Matrix n n R) (hZZi : Z * Zi = 1) :
    affineLineDet (Z * A * Zi) = affineLineDet A := by
  let c : R →+* R[X] := Polynomial.C
  let Ap := A.map c
  let Zp := Z.map c
  let Zip := Zi.map c
  have hZZip : Zp * Zip = 1 := by
    change (Z.map c) * (Zi.map c) = 1
    rw [← Matrix.map_mul, hZZi, Matrix.map_one] <;>
      first | exact map_zero c | exact map_one c
  have hmap : (Z * A * Zi).map c = Zp * Ap * Zip := by
    change (Z * A * Zi).map c = (Z.map c) * (A.map c) * (Zi.map c)
    rw [Matrix.map_mul, Matrix.map_mul] <;> exact map_zero c
  have hmatrix :
      (1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
          ((Z * A * Zi).map c - 1) =
        Zp * ((1 : Matrix n n R[X]) +
          (Polynomial.X : R[X]) • (Ap - 1)) * Zip := by
    rw [hmap]
    calc
      1 + (Polynomial.X : R[X]) • (Zp * Ap * Zip - 1) =
          Zp * Zip + (Polynomial.X : R[X]) •
            (Zp * Ap * Zip - Zp * Zip) := by rw [hZZip]
      _ = Zp * (1 + (Polynomial.X : R[X]) • (Ap - 1)) * Zip := by
        noncomm_ring
  rw [affineLineDet, affineLineDet, hmatrix,
    Matrix.det_mul, Matrix.det_mul]
  have hdet : Matrix.det Zp * Matrix.det Zip = 1 := by
    rw [← Matrix.det_mul, hZZip, Matrix.det_one]
  calc
    Matrix.det Zp * Matrix.det
          ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) • (Ap - 1)) *
        Matrix.det Zip =
      Matrix.det
          ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) • (Ap - 1)) *
        (Matrix.det Zp * Matrix.det Zip) := by ring
    _ = _ := by rw [hdet, mul_one]

/-- In the standard matrix-unit basis, left multiplication by `A` is the
Kronecker product of `A` with the identity matrix. -/
theorem leftMulMatrix_stdBasis_eq_kronecker
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.leftMulMatrix (Matrix.stdBasis R n n) A =
      Matrix.kronecker A (1 : Matrix n n R) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (A * Matrix.stdBasis R n n (k, l)) i j = _
  rw [Matrix.stdBasis_eq_single]
  by_cases hjl : j = l
  · subst l
    simp
  ·
    rw [Matrix.mul_single_apply_of_ne (hbj := hjl)]
    simp [hjl]

/-- The regular algebra norm on `M_n(R)` is `det^n`. -/
theorem algebraNorm_eq_det_pow_card
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.norm R A = Matrix.det A ^ Fintype.card n := by
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R n n),
    leftMulMatrix_stdBasis_eq_kronecker]
  change Matrix.det (Matrix.kroneckerMap (fun a b : R => a * b)
    A (1 : Matrix n n R)) = _
  rw [Matrix.det_kronecker]
  simp

/-- Over a field, the determinant attached to a splitting of an algebra is
independent of the chosen algebra equivalence with a matrix algebra. -/
theorem det_eq_of_algEquiv
    {K A n : Type*} [Field K] [Ring A] [Algebra K A]
    [Fintype n] [DecidableEq n]
    (e₁ e₂ : A ≃ₐ[K] Matrix n n K) (x : A) :
    Matrix.det (e₁ x) = Matrix.det (e₂ x) := by
  simpa using (Matrix.det_map (e₁.symm.trans e₂) (e₁ x)).symm

end Matrix

namespace Algebra

/-- In the scalar-extended basis, left multiplication by `1 ⊗ x` is the
entrywise scalar extension of the original left-multiplication matrix. -/
theorem leftMulMatrix_tensorProduct_includeRight
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis L b)
        (Algebra.TensorProduct.includeRight x) =
      (Algebra.leftMulMatrix b x).map (algebraMap K L) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp [Algebra.leftMulMatrix_eq_repr_mul]

/-- Regular algebra norm commutes with scalar extension, stated for the
canonical inclusion into a tensor product. -/
theorem norm_tensorProduct_includeRight
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.norm L (Algebra.TensorProduct.includeRight x :
        TensorProduct K L A) =
      algebraMap K L (Algebra.norm K x) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis L b),
    leftMulMatrix_tensorProduct_includeRight b x,
    Algebra.norm_eq_matrix_det b, RingHom.map_det]
  rfl

end Algebra
