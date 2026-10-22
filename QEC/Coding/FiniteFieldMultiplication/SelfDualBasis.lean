import QEC.Coding.FiniteFieldMultiplication.Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

open Polynomial
open scoped Matrix

namespace QEC.Coding

/-- The quotient root used by the fixed degree-eight carrier. -/
noncomputable def f256Alpha : F256 := AdjoinRoot.root f256Modulus

noncomputable instance : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2

private theorem f256Alpha_pow_eq_mk (k : ℕ) :
    f256Alpha ^ k = AdjoinRoot.mk f256Modulus (X ^ k) := by
  simp [f256Alpha, ← AdjoinRoot.mk_X]

/-- The selected quotient root lies on the seventeenth-cyclotomic boundary. -/
theorem f256Alpha_pow_seventeen : f256Alpha ^ 17 = 1 := by
  rw [f256Alpha_pow_eq_mk, ← (AdjoinRoot.mk f256Modulus).map_one,
    AdjoinRoot.mk_eq_mk]
  refine ⟨(X + 1) * (X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1), ?_⟩
  simp only [f256Modulus]
  ring_nf
  reduce_mod_char

/-- The selected quotient root is not the unit element. -/
theorem f256Alpha_ne_one : f256Alpha ≠ 1 := by
  intro h
  have hroot := AdjoinRoot.eval₂_root f256Modulus
  have h' : AdjoinRoot.root f256Modulus = 1 := by simpa [f256Alpha] using h
  rw [h'] at hroot
  norm_num [f256Modulus, eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_C] at hroot
  exact (by norm_num : ¬ 2 ∣ 5) ((CharP.cast_eq_zero_iff F256 2 5).mp hroot)

private theorem f256_trace_alpha_pow_0 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 0) = 0 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [f256_finrank, Nat.card_zmod]
  exact CharP.ofNat_eq_zero' (R := F256) 2 8 (by norm_num)

private theorem f256_mk_eq_of_dvd_sub {p q : Polynomial (ZMod 2)}
    (h : f256Modulus ∣ p - q) :
    AdjoinRoot.mk f256Modulus p = AdjoinRoot.mk f256Modulus q := by
  calc
    AdjoinRoot.mk f256Modulus p =
        AdjoinRoot.mk f256Modulus (p %ₘ f256Modulus) := by
          symm
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic
              (AdjoinRoot.mk f256Modulus p))
    _ = AdjoinRoot.mk f256Modulus (q %ₘ f256Modulus) := by
          rw [Polynomial.modByMonic_eq_of_dvd_sub f256Modulus_monic h]
    _ = AdjoinRoot.mk f256Modulus q := by
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic
              (AdjoinRoot.mk f256Modulus q))

private theorem f256_frobenius_sum_one :
    f256Alpha + f256Alpha ^ 2 + f256Alpha ^ 4 + f256Alpha ^ 8 +
      f256Alpha ^ 16 + f256Alpha ^ 15 + f256Alpha ^ 13 + f256Alpha ^ 9 = 0 := by
  have hmk :
      AdjoinRoot.mk f256Modulus
          (X ^ 16 + X ^ 15 + X ^ 13 + X ^ 9 + X ^ 8 + X ^ 4 + X ^ 2 + X) =
        AdjoinRoot.mk f256Modulus 0 := by
    apply f256_mk_eq_of_dvd_sub
    refine ⟨X ^ 8 + X ^ 7 + X ^ 2 + X, ?_⟩
    simp only [f256Modulus]
    ring_nf
    reduce_mod_char
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_zero, f256Alpha,
    add_comm, add_left_comm, add_assoc] using hmk

private theorem f256_trace_alpha_pow_1 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 1) = 0 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  rw [pow_eq_pow_mod 128 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 64 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 32 f256Alpha_pow_seventeen]
  simpa only [Nat.reduceMod, pow_one] using f256_frobenius_sum_one

private theorem f256_frobenius_sum_three :
    f256Alpha ^ 3 + f256Alpha ^ 6 + f256Alpha ^ 12 + f256Alpha ^ 7 +
      f256Alpha ^ 14 + f256Alpha ^ 11 + f256Alpha ^ 5 + f256Alpha ^ 10 = 1 := by
  have hmk :
      AdjoinRoot.mk f256Modulus
          (X ^ 14 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3) =
        AdjoinRoot.mk f256Modulus 1 := by
    apply f256_mk_eq_of_dvd_sub
    refine ⟨X ^ 6 + X ^ 4 + 1, ?_⟩
    simp only [f256Modulus]
    ring_nf
    reduce_mod_char
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, f256Alpha,
    add_comm, add_left_comm, add_assoc] using hmk

private theorem f256_trace_alpha_pow_3 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) = 1 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  rw [pow_eq_pow_mod 384 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 192 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 96 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 48 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 24 f256Alpha_pow_seventeen]
  simpa only [Nat.reduceMod] using f256_frobenius_sum_three

private theorem f256Alpha_pow_256_mul (k : ℕ) :
    f256Alpha ^ (256 * k) = f256Alpha ^ k := by
  calc
    f256Alpha ^ (256 * k) = f256Alpha ^ (k + 17 * (15 * k)) := by
      congr 1
      ring
    _ = f256Alpha ^ k * f256Alpha ^ (17 * (15 * k)) := by
      rw [pow_add]
    _ = f256Alpha ^ k * (f256Alpha ^ 17) ^ (15 * k) := by
      rw [pow_mul]
    _ = f256Alpha ^ k := by rw [f256Alpha_pow_seventeen, one_pow, mul_one]

private theorem f256_trace_alpha_pow_two_mul (k : ℕ) :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ (2 * k)) =
      Algebra.trace (ZMod 2) F256 (f256Alpha ^ k) := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  have h256 : (2 * k) * 128 = 256 * k := by ring
  rw [h256, f256Alpha_pow_256_mul]
  ring

private theorem f256_trace_alpha_pow_2 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 1) := by
          simpa using f256_trace_alpha_pow_two_mul 1
    _ = 0 := f256_trace_alpha_pow_1

private theorem f256_trace_alpha_pow_4 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) := by
          simpa using f256_trace_alpha_pow_two_mul 2
    _ = 0 := f256_trace_alpha_pow_2

private theorem f256_trace_alpha_pow_8 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) := by
          simpa using f256_trace_alpha_pow_two_mul 4
    _ = 0 := f256_trace_alpha_pow_4

private theorem f256_trace_alpha_pow_15 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) = 0 := by
  have h32 : f256Alpha ^ 32 = f256Alpha ^ 15 := by
    rw [pow_eq_pow_mod 32 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 32) := by rw [h32]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 16) := by
          simpa using f256_trace_alpha_pow_two_mul 16
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) := by
          simpa using f256_trace_alpha_pow_two_mul 8
    _ = 0 := f256_trace_alpha_pow_8

private theorem f256_trace_alpha_pow_13 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) = 0 := by
  have h30 : f256Alpha ^ 30 = f256Alpha ^ 13 := by
    rw [pow_eq_pow_mod 30 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 30) := by rw [h30]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) := by
          simpa using f256_trace_alpha_pow_two_mul 15
    _ = 0 := f256_trace_alpha_pow_15

private theorem f256_trace_alpha_pow_9 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 9) = 0 := by
  have h26 : f256Alpha ^ 26 = f256Alpha ^ 9 := by
    rw [pow_eq_pow_mod 26 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 9) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 26) := by rw [h26]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) := by
          simpa using f256_trace_alpha_pow_two_mul 13
    _ = 0 := f256_trace_alpha_pow_13

private theorem f256_trace_alpha_pow_6 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          simpa using f256_trace_alpha_pow_two_mul 3
    _ = 1 := f256_trace_alpha_pow_3

private theorem f256_trace_alpha_pow_12 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) := by
          simpa using f256_trace_alpha_pow_two_mul 6
    _ = 1 := f256_trace_alpha_pow_6

private theorem f256_trace_alpha_pow_7 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) = 1 := by
  have h24 : f256Alpha ^ 24 = f256Alpha ^ 7 := by
    rw [pow_eq_pow_mod 24 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 24) := by rw [h24]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) := by
          simpa using f256_trace_alpha_pow_two_mul 12
    _ = 1 := f256_trace_alpha_pow_12

private theorem f256_trace_alpha_pow_14 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) := by
          simpa using f256_trace_alpha_pow_two_mul 7
    _ = 1 := f256_trace_alpha_pow_7

private theorem f256_trace_alpha_pow_11 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) = 1 := by
  have h28 : f256Alpha ^ 28 = f256Alpha ^ 11 := by
    rw [pow_eq_pow_mod 28 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 28) := by rw [h28]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) := by
          simpa using f256_trace_alpha_pow_two_mul 14
    _ = 1 := f256_trace_alpha_pow_14

private theorem f256_trace_alpha_pow_5 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) = 1 := by
  have h22 : f256Alpha ^ 22 = f256Alpha ^ 5 := by
    rw [pow_eq_pow_mod 22 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 22) := by rw [h22]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) := by
          simpa using f256_trace_alpha_pow_two_mul 11
    _ = 1 := f256_trace_alpha_pow_11

private theorem f256_trace_alpha_pow_10 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 10) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 10) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) := by
          simpa using f256_trace_alpha_pow_two_mul 5
    _ = 1 := f256_trace_alpha_pow_5

private theorem f256_trace_alpha_pow_table (k : Fin 15) :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ (k : ℕ)) =
      ![0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1] k := by
  fin_cases k
  · simpa using f256_trace_alpha_pow_0
  · simpa using f256_trace_alpha_pow_1
  · simpa using f256_trace_alpha_pow_2
  · simpa using f256_trace_alpha_pow_3
  · simpa using f256_trace_alpha_pow_4
  · simpa using f256_trace_alpha_pow_5
  · simpa using f256_trace_alpha_pow_6
  · simpa using f256_trace_alpha_pow_7
  · simpa using f256_trace_alpha_pow_8
  · simpa using f256_trace_alpha_pow_9
  · simpa using f256_trace_alpha_pow_10
  · simpa using f256_trace_alpha_pow_11
  · simpa using f256_trace_alpha_pow_12
  · simpa using f256_trace_alpha_pow_13
  · simpa using f256_trace_alpha_pow_14

theorem f256PolynomialBasis_apply (i : Fin 8) :
    f256PolynomialBasis i = f256Alpha ^ (i : ℕ) := by
  rw [f256PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f256Modulus_monic).basis_eq_pow]
  rfl

/-- The certified column-coordinate matrix for the chosen binary basis. -/
def f256SelfDualP : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 1, 1, 0;
     0, 0, 0, 1, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1, 1, 1]

/-- The independently checked inverse of `f256SelfDualP`. -/
def f256SelfDualPInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 1, 0, 1;
     1, 1, 0, 0, 1, 0, 1, 0;
     1, 1, 0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0, 1, 0;
     1, 1, 0, 0, 0, 1, 0, 0;
     1, 1, 0, 0, 0, 1, 1, 0]

/-- The polynomial-basis trace Gram matrix certified from the quotient trace route. -/
def f256PolynomialTraceGram : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1, 1, 0;
     0, 1, 0, 1, 1, 1, 0, 0;
     1, 0, 1, 1, 1, 0, 0, 1;
     0, 1, 1, 1, 0, 0, 1, 1;
     1, 1, 1, 0, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1, 1, 0;
     1, 0, 0, 1, 1, 1, 0, 1]

theorem f256PolynomialTraceMatrix_eq :
    Algebra.traceMatrix (ZMod 2) f256PolynomialBasis = f256PolynomialTraceGram := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialBasis_apply, ← pow_add]
  fin_cases i <;> fin_cases j <;>
    norm_num [f256PolynomialTraceGram, f256_trace_alpha_pow_0,
      f256_trace_alpha_pow_1, f256_trace_alpha_pow_2, f256_trace_alpha_pow_3,
      f256_trace_alpha_pow_4, f256_trace_alpha_pow_5, f256_trace_alpha_pow_6,
      f256_trace_alpha_pow_7, f256_trace_alpha_pow_8, f256_trace_alpha_pow_9,
      f256_trace_alpha_pow_10, f256_trace_alpha_pow_11, f256_trace_alpha_pow_12,
      f256_trace_alpha_pow_13, f256_trace_alpha_pow_14] <;>
    first
    | simpa only [pow_zero] using f256_trace_alpha_pow_0
    | simpa only [pow_one] using f256_trace_alpha_pow_1

theorem f256SelfDualP_mul_inv : f256SelfDualP * f256SelfDualPInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem f256SelfDualPInv_mul : f256SelfDualPInv * f256SelfDualP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem f256SelfDualP_det : f256SelfDualP.det = 1 := by
  have hdet : f256SelfDualP.det * f256SelfDualPInv.det = 1 := by
    rw [← Matrix.det_mul, f256SelfDualP_mul_inv, Matrix.det_one]
  have hne : f256SelfDualP.det ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hdet
    exact zero_ne_one hdet
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hne

theorem f256SelfDualP_det_isUnit : IsUnit f256SelfDualP.det := by
  rw [f256SelfDualP_det]
  exact isUnit_one

theorem f256SelfDualP_transpose_mul_gram_mul :
    f256SelfDualP.transpose * f256PolynomialTraceGram * f256SelfDualP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The actual coordinate change induced by the displayed invertible matrix. -/
noncomputable def f256SelfDualChange : F256 ≃ₗ[ZMod 2] F256 :=
  Matrix.toLinearEquiv f256PolynomialBasis f256SelfDualP f256SelfDualP_det_isUnit

/-- The explicit binary basis obtained from the polynomial basis by `f256SelfDualP`. -/
noncomputable def f256SelfDualBasis : Module.Basis (Fin 8) (ZMod 2) F256 :=
  f256PolynomialBasis.map f256SelfDualChange

theorem f256SelfDualBasis_apply (i : Fin 8) :
    f256SelfDualBasis i =
      (f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256)) i := by
  rw [f256SelfDualBasis, Module.Basis.map_apply, f256SelfDualChange]
  change Matrix.toLin f256PolynomialBasis f256PolynomialBasis f256SelfDualP
      (f256PolynomialBasis i) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.vecMul, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

theorem f256SelfDualBasis_traceMatrix :
    Algebra.traceMatrix (ZMod 2) f256SelfDualBasis = 1 := by
  have hbasis : (f256SelfDualBasis : Fin 8 → F256) =
      f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256) := by
    funext i
    exact f256SelfDualBasis_apply i
  calc
    Algebra.traceMatrix (ZMod 2) f256SelfDualBasis =
        Algebra.traceMatrix (ZMod 2)
          (f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256)) := by
            rw [hbasis]
    _ = f256SelfDualP.transpose * Algebra.traceMatrix (ZMod 2) f256PolynomialBasis *
        f256SelfDualP :=
          Algebra.traceMatrix_of_matrix_vecMul f256PolynomialBasis f256SelfDualP
    _ = f256SelfDualP.transpose * f256PolynomialTraceGram * f256SelfDualP := by
          rw [f256PolynomialTraceMatrix_eq]
    _ = 1 := f256SelfDualP_transpose_mul_gram_mul

theorem f256SelfDualBasis_trace_mul (i j : Fin 8) :
    Algebra.trace (ZMod 2) F256 (f256SelfDualBasis i * f256SelfDualBasis j) =
      if j = i then 1 else 0 := by
  have hentry := congr_fun (congr_fun f256SelfDualBasis_traceMatrix i) j
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply,
    Pi.single_apply, eq_comm] using hentry

theorem f256SelfDualBasis_traceDual :
    f256SelfDualBasis.traceDual = f256SelfDualBasis := by
  have hfun : (f256SelfDualBasis.traceDual : Fin 8 → F256) =
      (f256SelfDualBasis : Fin 8 → F256) := by
    apply Module.Basis.traceDual_eq_iff.mpr
    intro i j
    simpa only [Algebra.traceForm_apply] using f256SelfDualBasis_trace_mul i j
  apply DFunLike.ext _ _
  intro i
  exact congr_fun hfun i

end QEC.Coding
