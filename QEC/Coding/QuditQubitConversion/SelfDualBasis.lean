import QEC.Coding.QuditQubitConversion.FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

open Polynomial
open scoped Matrix

namespace QEC.Coding

noncomputable instance : CharP F1024 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F1024).injective 2

private theorem f1024Alpha_pow_eq_mk' (k : ℕ) :
    f1024Alpha ^ k = AdjoinRoot.mk f1024Modulus (X ^ k) := by
  simp [f1024Alpha, ← AdjoinRoot.mk_X]

private theorem f1024_square_residue (p r q : Polynomial (ZMod 2))
    (h : p ^ 2 = f1024Modulus * q + r) :
    (AdjoinRoot.mk f1024Modulus p) ^ 2 = AdjoinRoot.mk f1024Modulus r := by
  rw [← (AdjoinRoot.mk f1024Modulus).map_pow, h, map_add, map_mul,
    AdjoinRoot.mk_self, zero_mul, zero_add]

private theorem f1024_trace_alpha_pow_3 :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 3) = 0 := by
  have h0 : f1024Alpha ^ 3 = AdjoinRoot.mk f1024Modulus (X ^ 3) :=
    f1024Alpha_pow_eq_mk' 3
  have h1 : f1024Alpha ^ 6 = AdjoinRoot.mk f1024Modulus (X ^ 6) := by
    calc
      f1024Alpha ^ 6 = (f1024Alpha ^ 3) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 3)) ^ 2 := by rw [h0]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 6) := by
        apply f1024_square_residue (X ^ 3) (X ^ 6) 0
        ring
  have h2 : f1024Alpha ^ 12 = AdjoinRoot.mk f1024Modulus (X ^ 5 + X ^ 2) := by
    calc
      f1024Alpha ^ 12 = (f1024Alpha ^ 6) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 6)) ^ 2 := by rw [h1]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 5 + X ^ 2) := by
        apply f1024_square_residue (X ^ 6) (X ^ 5 + X ^ 2) (X ^ 2)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h3 : f1024Alpha ^ 24 = AdjoinRoot.mk f1024Modulus (X ^ 4 + X ^ 3 + 1) := by
    calc
      f1024Alpha ^ 24 = (f1024Alpha ^ 12) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 5 + X ^ 2)) ^ 2 := by rw [h2]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 4 + X ^ 3 + 1) := by
        apply f1024_square_residue (X ^ 5 + X ^ 2) (X ^ 4 + X ^ 3 + 1) 1
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h4 : f1024Alpha ^ 48 = AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 6 + 1) := by
    calc
      f1024Alpha ^ 48 = (f1024Alpha ^ 24) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 4 + X ^ 3 + 1)) ^ 2 := by rw [h3]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 6 + 1) := by
        apply f1024_square_residue (X ^ 4 + X ^ 3 + 1) (X ^ 8 + X ^ 6 + 1) 0
        ring_nf
        reduce_mod_char
  have h5 : f1024Alpha ^ 96 =
      AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1) := by
    calc
      f1024Alpha ^ 96 = (f1024Alpha ^ 48) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 6 + 1)) ^ 2 := by rw [h4]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1) := by
        apply f1024_square_residue (X ^ 8 + X ^ 6 + 1)
          (X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1) (X ^ 6 + X ^ 2)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h6 : f1024Alpha ^ 192 =
      AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + X) := by
    calc
      f1024Alpha ^ 192 = (f1024Alpha ^ 96) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1)) ^ 2 := by rw [h5]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + X) := by
        apply f1024_square_residue (X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1)
          (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + X) (X ^ 8 + X ^ 2 + X + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h7 : f1024Alpha ^ 384 =
      AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 4 + X ^ 3 + X ^ 2 + 1) := by
    calc
      f1024Alpha ^ 384 = (f1024Alpha ^ 192) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + X)) ^ 2 := by rw [h6]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 4 + X ^ 3 + X ^ 2 + 1) := by
        apply f1024_square_residue (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + X)
          (X ^ 9 + X ^ 4 + X ^ 3 + X ^ 2 + 1) (X ^ 6 + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h8 : f1024Alpha ^ 768 = AdjoinRoot.mk f1024Modulus (X ^ 6 + X + 1) := by
    calc
      f1024Alpha ^ 768 = (f1024Alpha ^ 384) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 4 + X ^ 3 + X ^ 2 + 1)) ^ 2 := by rw [h7]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 6 + X + 1) := by
        apply f1024_square_residue (X ^ 9 + X ^ 4 + X ^ 3 + X ^ 2 + 1) (X ^ 6 + X + 1)
          (X ^ 8 + X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h9 : f1024Alpha ^ 1536 = AdjoinRoot.mk f1024Modulus (X ^ 5 + 1) := by
    calc
      f1024Alpha ^ 1536 = (f1024Alpha ^ 768) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 6 + X + 1)) ^ 2 := by rw [h8]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 5 + 1) := by
        apply f1024_square_residue (X ^ 6 + X + 1) (X ^ 5 + 1) (X ^ 2)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have hsum :
      f1024Alpha ^ 3 + f1024Alpha ^ 6 + f1024Alpha ^ 12 + f1024Alpha ^ 24 +
        f1024Alpha ^ 48 + f1024Alpha ^ 96 + f1024Alpha ^ 192 +
          f1024Alpha ^ 384 + f1024Alpha ^ 768 + f1024Alpha ^ 1536 = 0 := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
    ring_nf
    have htwo : (2 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
    have hfour : (4 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 4 (by norm_num)
    have hsix : (6 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 6 (by norm_num)
    rw [htwo, hfour, hsix]
    ring
  apply (algebraMap (ZMod 2) F1024).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f1024_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  exact hsum

private theorem f1024_trace_alpha :
    Algebra.trace (ZMod 2) F1024 f1024Alpha = 0 := by
  letI : Nontrivial F1024 :=
    AdjoinRoot.nontrivial f1024Modulus (by
      rw [degree_eq_natDegree f1024Modulus_monic.ne_zero, f1024Modulus_natDegree]
      norm_num)
  change Algebra.trace (ZMod 2) F1024
    (AdjoinRoot.powerBasis' f1024Modulus_monic).gen = 0
  rw [(AdjoinRoot.powerBasis' f1024Modulus_monic).trace_gen_eq_nextCoeff_minpoly]
  change -(minpoly (ZMod 2) (AdjoinRoot.root f1024Modulus)).nextCoeff = 0
  rw [AdjoinRoot.minpoly_root f1024Modulus_monic.ne_zero]
  rw [f1024Modulus_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  change -f1024Modulus.nextCoeff = 0
  rw [nextCoeff, f1024Modulus_natDegree]
  norm_num [f1024Modulus, coeff_add, coeff_X_pow, coeff_one]

private theorem f1024_trace_alpha_pow_1 :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 1) = 0 := by
  simpa only [pow_one] using f1024_trace_alpha

private theorem f1024_trace_alpha_pow_0 :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 0) = 0 := by
  apply (algebraMap (ZMod 2) F1024).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [f1024_finrank, Nat.card_zmod]
  exact CharP.ofNat_eq_zero' (R := F1024) 2 10 (by norm_num)

private theorem f1024_trace_sq (x : F1024) :
    Algebra.trace (ZMod 2) F1024 (x ^ 2) = Algebra.trace (ZMod 2) F1024 x := by
  apply (algebraMap (ZMod 2) F1024).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f1024_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  have hx : x ^ 1024 = x := by
    rw [← f1024_card]
    exact FiniteField.pow_card x
  rw [hx]
  ring

private theorem f1024_trace_alpha_pow_7 :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 7) = 1 := by
  have h0 : f1024Alpha ^ 7 = AdjoinRoot.mk f1024Modulus (X ^ 7) := f1024Alpha_pow_eq_mk' 7
  have h1 : f1024Alpha ^ 14 = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 4) := by
    calc
      f1024Alpha ^ 14 = (f1024Alpha ^ 7) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 7)) ^ 2 := by rw [h0]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 4) := by
        apply f1024_square_residue (X ^ 7) (X ^ 7 + X ^ 4) (X ^ 4)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h2 : f1024Alpha ^ 28 = AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 7 + X ^ 4) := by
    calc
      f1024Alpha ^ 28 = (f1024Alpha ^ 14) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 4)) ^ 2 := by rw [h1]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 7 + X ^ 4) := by
        apply f1024_square_residue (X ^ 7 + X ^ 4) (X ^ 8 + X ^ 7 + X ^ 4) (X ^ 4)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h3 : f1024Alpha ^ 56 =
      AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4) := by
    calc
      f1024Alpha ^ 56 = (f1024Alpha ^ 28) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 7 + X ^ 4)) ^ 2 := by rw [h2]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4) := by
        apply f1024_square_residue (X ^ 8 + X ^ 7 + X ^ 4)
          (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4) (X ^ 6 + X ^ 4)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h4 : f1024Alpha ^ 112 =
      AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X) := by
    calc
      f1024Alpha ^ 112 = (f1024Alpha ^ 56) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4)) ^ 2 := by rw [h3]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X) := by
        apply f1024_square_residue (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4)
          (X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X)
          (X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h5 : f1024Alpha ^ 224 =
      AdjoinRoot.mk f1024Modulus (X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1) := by
    calc
      f1024Alpha ^ 224 = (f1024Alpha ^ 112) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X)) ^ 2 := by rw [h4]
      _ = AdjoinRoot.mk f1024Modulus
          (X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1) := by
        apply f1024_square_residue (X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X)
          (X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1)
          (X ^ 8 + X ^ 4 + X ^ 2 + X + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h6 : f1024Alpha ^ 448 =
      AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2) := by
    calc
      f1024Alpha ^ 448 = (f1024Alpha ^ 224) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1)) ^ 2 := by rw [h5]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2) := by
        apply f1024_square_residue (X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1)
          (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2) (X ^ 6 + X ^ 4 + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h7 : f1024Alpha ^ 896 = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 7 + X ^ 4 + X) := by
    calc
      f1024Alpha ^ 896 = (f1024Alpha ^ 448) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2)) ^ 2 := by rw [h6]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 7 + X ^ 4 + X) := by
        apply f1024_square_residue (X ^ 9 + X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2)
          (X ^ 9 + X ^ 7 + X ^ 4 + X) (X ^ 8 + X ^ 6 + X ^ 4 + X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h8 : f1024Alpha ^ 1792 = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 2 + X) := by
    calc
      f1024Alpha ^ 1792 = (f1024Alpha ^ 896) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 9 + X ^ 7 + X ^ 4 + X)) ^ 2 := by rw [h7]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 2 + X) := by
        apply f1024_square_residue (X ^ 9 + X ^ 7 + X ^ 4 + X) (X ^ 7 + X ^ 2 + X)
          (X ^ 8 + X ^ 4 + X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h9 : f1024Alpha ^ 3584 = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 2) := by
    calc
      f1024Alpha ^ 3584 = (f1024Alpha ^ 1792) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 2 + X)) ^ 2 := by rw [h8]
      _ = AdjoinRoot.mk f1024Modulus (X ^ 7 + X ^ 2) := by
        apply f1024_square_residue (X ^ 7 + X ^ 2 + X) (X ^ 7 + X ^ 2) (X ^ 4)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have hsum :
      f1024Alpha ^ 7 + f1024Alpha ^ 14 + f1024Alpha ^ 28 + f1024Alpha ^ 56 +
        f1024Alpha ^ 112 + f1024Alpha ^ 224 + f1024Alpha ^ 448 +
          f1024Alpha ^ 896 + f1024Alpha ^ 1792 + f1024Alpha ^ 3584 = 1 := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
    ring_nf
    have htwo : (2 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
    have hfour : (4 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 4 (by norm_num)
    have hsix : (6 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 6 (by norm_num)
    have hten : (10 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 10 (by norm_num)
    rw [htwo, hfour, hsix, hten]
    ring
  apply (algebraMap (ZMod 2) F1024).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f1024_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  exact hsum

private theorem f1024_alpha_pow_ten_add (k : ℕ) :
    f1024Alpha ^ (10 + k) = f1024Alpha ^ k + f1024Alpha ^ (3 + k) := by
  calc
    f1024Alpha ^ (10 + k) = f1024Alpha ^ 10 * f1024Alpha ^ k := by rw [pow_add]
    _ = (1 + f1024Alpha ^ 3) * f1024Alpha ^ k := by rw [f1024Alpha_pow_ten]
    _ = f1024Alpha ^ k + f1024Alpha ^ (3 + k) := by rw [pow_add]; ring

private theorem f1024_trace_alpha_pow_2 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 2) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 2) = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 1) := by
      simpa only [pow_one] using f1024_trace_sq f1024Alpha
    _ = 0 := f1024_trace_alpha_pow_1

private theorem f1024_trace_alpha_pow_4 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 4) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 4) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 2) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 2) := f1024_trace_sq (f1024Alpha ^ 2)
    _ = 0 := f1024_trace_alpha_pow_2

private theorem f1024_trace_alpha_pow_6 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 6) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 6) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 3) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 3) := f1024_trace_sq (f1024Alpha ^ 3)
    _ = 0 := f1024_trace_alpha_pow_3

private theorem f1024_trace_alpha_pow_8 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 8) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 8) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 4) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 4) := f1024_trace_sq (f1024Alpha ^ 4)
    _ = 0 := f1024_trace_alpha_pow_4

private theorem f1024_trace_alpha_pow_12 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 12) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 12) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 6) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 6) := f1024_trace_sq (f1024Alpha ^ 6)
    _ = 0 := f1024_trace_alpha_pow_6

private theorem f1024_trace_alpha_pow_14 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 14) = 1 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 14) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 7) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 7) := f1024_trace_sq (f1024Alpha ^ 7)
    _ = 1 := f1024_trace_alpha_pow_7

private theorem f1024_trace_alpha_pow_16 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 16) = 0 := by
  calc
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 16) = Algebra.trace (ZMod 2) F1024 ((f1024Alpha ^ 8) ^ 2) := by ring
    _ = Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 8) := f1024_trace_sq (f1024Alpha ^ 8)
    _ = 0 := f1024_trace_alpha_pow_8

private theorem f1024_trace_alpha_pow_5 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 5) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 2
  have htrace : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 12) =
      Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 2) + Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 5) := by
    rw [hpow, map_add]
  rw [f1024_trace_alpha_pow_12, f1024_trace_alpha_pow_2] at htrace
  simpa using htrace.symm

private theorem f1024_trace_alpha_pow_9 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 9) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 6
  have htrace : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 16) =
      Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 6) + Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 9) := by
    rw [hpow, map_add]
  rw [f1024_trace_alpha_pow_16, f1024_trace_alpha_pow_6] at htrace
  simpa using htrace.symm

private theorem f1024_trace_alpha_pow_10 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 10) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 0
  rw [show 10 + 0 = 10 by norm_num, show 3 + 0 = 3 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_0, f1024_trace_alpha_pow_3]
  rfl

private theorem f1024_trace_alpha_pow_11 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 11) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 1
  rw [show 10 + 1 = 11 by norm_num, show 3 + 1 = 4 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_1, f1024_trace_alpha_pow_4]
  rfl

private theorem f1024_trace_alpha_pow_13 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 13) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 3
  rw [show 10 + 3 = 13 by norm_num, show 3 + 3 = 6 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_3, f1024_trace_alpha_pow_6]
  rfl

private theorem f1024_trace_alpha_pow_15 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 15) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 5
  rw [show 10 + 5 = 15 by norm_num, show 3 + 5 = 8 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_5, f1024_trace_alpha_pow_8]
  rfl

private theorem f1024_trace_alpha_pow_17 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 17) = 1 := by
  have hpow := f1024_alpha_pow_ten_add 7
  rw [show 10 + 7 = 17 by norm_num, show 3 + 7 = 10 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_7, f1024_trace_alpha_pow_10]
  rfl

private theorem f1024_trace_alpha_pow_18 : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 18) = 0 := by
  have hpow := f1024_alpha_pow_ten_add 8
  rw [show 10 + 8 = 18 by norm_num, show 3 + 8 = 11 by norm_num] at hpow
  rw [hpow, map_add, f1024_trace_alpha_pow_8, f1024_trace_alpha_pow_11]
  rfl

private theorem f1024_trace_alpha_pow_table (k : Fin 19) :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ (k : ℕ)) =
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] k := by
  fin_cases k
  · simpa using f1024_trace_alpha_pow_0
  · simpa using f1024_trace_alpha_pow_1
  · simpa using f1024_trace_alpha_pow_2
  · simpa using f1024_trace_alpha_pow_3
  · simpa using f1024_trace_alpha_pow_4
  · simpa using f1024_trace_alpha_pow_5
  · simpa using f1024_trace_alpha_pow_6
  · simpa using f1024_trace_alpha_pow_7
  · simpa using f1024_trace_alpha_pow_8
  · simpa using f1024_trace_alpha_pow_9
  · simpa using f1024_trace_alpha_pow_10
  · simpa using f1024_trace_alpha_pow_11
  · simpa using f1024_trace_alpha_pow_12
  · simpa using f1024_trace_alpha_pow_13
  · simpa using f1024_trace_alpha_pow_14
  · simpa using f1024_trace_alpha_pow_15
  · simpa using f1024_trace_alpha_pow_16
  · simpa using f1024_trace_alpha_pow_17
  · simpa using f1024_trace_alpha_pow_18

theorem f1024PolynomialBasis_apply (i : Fin 10) :
    f1024PolynomialBasis i = f1024Alpha ^ (i : ℕ) := by
  rw [f1024PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f1024Modulus_monic).basis_eq_pow]
  rfl

/-- Columns are the ten source-displayed self-dual vectors, in the fixed polynomial basis. -/
def f1024SelectedSelfDualP : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1, 0, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     0, 1, 0, 1, 0, 1, 0, 0, 1, 0;
     1, 0, 0, 1, 1, 0, 0, 0, 0, 1;
     1, 0, 1, 0, 1, 0, 0, 1, 0, 0;
     0, 1, 0, 1, 0, 0, 1, 0, 0, 1;
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0, 0, 0, 0, 0]

/-- An independently selected inverse, validated in both directions below. -/
def f1024SelectedSelfDualPInv : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1, 1, 0, 0, 0;
     1, 1, 0, 0, 1, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 0, 0, 0, 1, 1, 0;
     1, 1, 0, 1, 1, 0, 0, 0, 0, 1;
     1, 0, 1, 1, 0, 1, 1, 0, 1, 1;
     1, 0, 0, 0, 1, 1, 1, 1, 0, 0;
     1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     1, 0, 1, 0, 0, 1, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 1, 0, 0, 0, 0, 1, 0]

def f1024PolynomialTraceGram : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 1, 0, 0, 1, 0]

theorem f1024PolynomialTraceMatrix_eq :
    Algebra.traceMatrix (ZMod 2) f1024PolynomialBasis = f1024PolynomialTraceGram := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f1024PolynomialBasis_apply, f1024PolynomialBasis_apply, ← pow_add]
  have hlt : (i : ℕ) + (j : ℕ) < 19 := by omega
  rw [f1024_trace_alpha_pow_table ⟨(i : ℕ) + (j : ℕ), hlt⟩]
  fin_cases i <;> fin_cases j <;> norm_num [f1024PolynomialTraceGram]

theorem f1024SelectedSelfDualP_mul_inv :
    f1024SelectedSelfDualP * f1024SelectedSelfDualPInv = 1 := by decide

theorem f1024SelectedSelfDualPInv_mul :
    f1024SelectedSelfDualPInv * f1024SelectedSelfDualP = 1 := by decide

theorem f1024SelectedSelfDualP_det_isUnit : IsUnit f1024SelectedSelfDualP.det :=
  Matrix.isUnit_det_of_right_inverse f1024SelectedSelfDualP_mul_inv

theorem f1024SelectedSelfDualP_transpose_mul_gram_mul :
    f1024SelectedSelfDualP.transpose * f1024PolynomialTraceGram * f1024SelectedSelfDualP = 1 := by decide

noncomputable def f1024SelectedSelfDualChange : F1024 ≃ₗ[ZMod 2] F1024 :=
  Matrix.toLinearEquiv f1024PolynomialBasis f1024SelectedSelfDualP f1024SelectedSelfDualP_det_isUnit

noncomputable def f1024SelectedSelfDualBasis : Module.Basis (Fin 10) (ZMod 2) F1024 :=
  f1024PolynomialBasis.map f1024SelectedSelfDualChange

theorem f1024SelectedSelfDualBasis_apply (i : Fin 10) :
    f1024SelectedSelfDualBasis i =
      (f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) i := by
  rw [f1024SelectedSelfDualBasis, Module.Basis.map_apply, f1024SelectedSelfDualChange]
  change Matrix.toLin f1024PolynomialBasis f1024PolynomialBasis f1024SelectedSelfDualP
      (f1024PolynomialBasis i) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.vecMul, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

theorem f1024SelectedSelfDualBasis_traceMatrix :
    Algebra.traceMatrix (ZMod 2) f1024SelectedSelfDualBasis = 1 := by
  have hbasis : (f1024SelectedSelfDualBasis : Fin 10 → F1024) =
      f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024) := by
    funext i
    exact f1024SelectedSelfDualBasis_apply i
  calc
    Algebra.traceMatrix (ZMod 2) f1024SelectedSelfDualBasis =
        Algebra.traceMatrix (ZMod 2)
          (f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) := by
            rw [hbasis]
    _ = f1024SelectedSelfDualP.transpose * Algebra.traceMatrix (ZMod 2) f1024PolynomialBasis *
        f1024SelectedSelfDualP :=
          Algebra.traceMatrix_of_matrix_vecMul f1024PolynomialBasis f1024SelectedSelfDualP
    _ = f1024SelectedSelfDualP.transpose * f1024PolynomialTraceGram * f1024SelectedSelfDualP := by
          rw [f1024PolynomialTraceMatrix_eq]
    _ = 1 := f1024SelectedSelfDualP_transpose_mul_gram_mul

theorem f1024SelectedSelfDualBasis_trace_mul (i j : Fin 10) :
    Algebra.trace (ZMod 2) F1024 (f1024SelectedSelfDualBasis i * f1024SelectedSelfDualBasis j) =
      if j = i then 1 else 0 := by
  have hentry := congr_fun (congr_fun f1024SelectedSelfDualBasis_traceMatrix i) j
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply,
    Pi.single_apply, eq_comm] using hentry

theorem f1024SelectedSelfDualBasis_traceDual :
    f1024SelectedSelfDualBasis.traceDual = f1024SelectedSelfDualBasis := by
  have hfun : (f1024SelectedSelfDualBasis.traceDual : Fin 10 → F1024) =
      (f1024SelectedSelfDualBasis : Fin 10 → F1024) := by
    apply Module.Basis.traceDual_eq_iff.mpr
    intro i j
    simpa only [Algebra.traceForm_apply] using f1024SelectedSelfDualBasis_trace_mul i j
  apply DFunLike.ext _ _
  intro i
  exact congr_fun hfun i

noncomputable def f1024SelectedCoordinates : F1024 ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  f1024SelectedSelfDualBasis.equivFun

theorem f1024SelectedCoordinates_symm_apply (x : F1024) :
    f1024SelectedCoordinates.symm (f1024SelectedCoordinates x) = x :=
  f1024SelectedCoordinates.symm_apply_apply x

theorem f1024SelectedCoordinates_apply_symm (c : Fin 10 → ZMod 2) :
    f1024SelectedCoordinates (f1024SelectedCoordinates.symm c) = c :=
  f1024SelectedCoordinates.apply_symm_apply c

end QEC.Coding
