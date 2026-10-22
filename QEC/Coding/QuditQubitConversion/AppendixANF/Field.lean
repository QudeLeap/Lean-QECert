import QEC.Coding.QuditQubitConversion.AppendixANF.SupportCertificate

/-!
# Field semantics for the WHY24 Appendix-A sparse ANF

This module proves that the fixed polynomial-coordinate multiplication table
used by the sparse certificate denotes multiplication in the concrete field
`F1024`.  It also identifies the selected-basis coordinate words and their
Frobenius powers.  No Boolean input word is enumerated here.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open scoped Matrix

/-- Evaluation of a polynomial-coordinate word in the concrete field. -/
noncomputable def polynomialEval : Word →ₗ[ZMod 2] F1024 where
  toFun word := ∑ power : Fin 10, word power • f1024Alpha ^ (power : Nat)
  map_add' left right := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar word := by
    change
      (∑ power : Fin 10, (scalar * word power) •
        f1024Alpha ^ (power : Nat)) =
        scalar • ∑ power : Fin 10,
          word power • f1024Alpha ^ (power : Nat)
    simp only [Finset.smul_sum, smul_smul]

theorem polynomialEval_single (coordinate : Fin 10) :
    polynomialEval (Pi.single coordinate (1 : ZMod 2)) =
      f1024Alpha ^ (coordinate : Nat) := by
  change
    (∑ power : Fin 10,
      (Pi.single coordinate (1 : ZMod 2) : Word) power •
        f1024Alpha ^ (power : Nat)) =
      f1024Alpha ^ (coordinate : Nat)
  rw [Fintype.sum_eq_single coordinate]
  · simp
  · intro power hpower
    simp [Pi.single_apply, hpower.symm]

private theorem alpha_pow_ten_add (n : Nat) :
    f1024Alpha ^ (10 + n) = f1024Alpha ^ n + f1024Alpha ^ (3 + n) := by
  calc
    f1024Alpha ^ (10 + n) = f1024Alpha ^ 10 * f1024Alpha ^ n := by
      rw [pow_add]
    _ = (1 + f1024Alpha ^ 3) * f1024Alpha ^ n := by
      rw [f1024Alpha_pow_ten]
    _ = f1024Alpha ^ n + f1024Alpha ^ (3 + n) := by
      rw [pow_add]
      ring

private theorem alphaReduction_eval_0 :
    polynomialEval (alphaReduction 0) = f1024Alpha ^ 0 := by
  have hrow : alphaReduction (0 : Fin 19) = Pi.single (0 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (0 : Fin 10)

private theorem alphaReduction_eval_1 :
    polynomialEval (alphaReduction 1) = f1024Alpha ^ 1 := by
  have hrow : alphaReduction (1 : Fin 19) = Pi.single (1 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (1 : Fin 10)

private theorem alphaReduction_eval_2 :
    polynomialEval (alphaReduction 2) = f1024Alpha ^ 2 := by
  have hrow : alphaReduction (2 : Fin 19) = Pi.single (2 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (2 : Fin 10)

private theorem alphaReduction_eval_3 :
    polynomialEval (alphaReduction 3) = f1024Alpha ^ 3 := by
  have hrow : alphaReduction (3 : Fin 19) = Pi.single (3 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (3 : Fin 10)

private theorem alphaReduction_eval_4 :
    polynomialEval (alphaReduction 4) = f1024Alpha ^ 4 := by
  have hrow : alphaReduction (4 : Fin 19) = Pi.single (4 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (4 : Fin 10)

private theorem alphaReduction_eval_5 :
    polynomialEval (alphaReduction 5) = f1024Alpha ^ 5 := by
  have hrow : alphaReduction (5 : Fin 19) = Pi.single (5 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (5 : Fin 10)

private theorem alphaReduction_eval_6 :
    polynomialEval (alphaReduction 6) = f1024Alpha ^ 6 := by
  have hrow : alphaReduction (6 : Fin 19) = Pi.single (6 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (6 : Fin 10)

private theorem alphaReduction_eval_7 :
    polynomialEval (alphaReduction 7) = f1024Alpha ^ 7 := by
  have hrow : alphaReduction (7 : Fin 19) = Pi.single (7 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (7 : Fin 10)

private theorem alphaReduction_eval_8 :
    polynomialEval (alphaReduction 8) = f1024Alpha ^ 8 := by
  have hrow : alphaReduction (8 : Fin 19) = Pi.single (8 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (8 : Fin 10)

private theorem alphaReduction_eval_9 :
    polynomialEval (alphaReduction 9) = f1024Alpha ^ 9 := by
  have hrow : alphaReduction (9 : Fin 19) = Pi.single (9 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (9 : Fin 10)

private theorem alphaReduction_eval_10 :
    polynomialEval (alphaReduction 10) = f1024Alpha ^ 10 := by
  have hrow : alphaReduction (10 : Fin 19) =
      Pi.single (0 : Fin 10) 1 + Pi.single (3 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 10 = 1 + f1024Alpha ^ 3 := by
    simpa using alpha_pow_ten_add 0
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_11 :
    polynomialEval (alphaReduction 11) = f1024Alpha ^ 11 := by
  have hrow : alphaReduction (11 : Fin 19) =
      Pi.single (1 : Fin 10) 1 + Pi.single (4 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 11 = f1024Alpha + f1024Alpha ^ 4 := by
    simpa using alpha_pow_ten_add 1
  simpa [hrow, polynomialEval_single] using hpower.symm

private theorem alphaReduction_eval_12 :
    polynomialEval (alphaReduction 12) = f1024Alpha ^ 12 := by
  have hrow : alphaReduction (12 : Fin 19) =
      Pi.single (2 : Fin 10) 1 + Pi.single (5 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 12 = f1024Alpha ^ 2 + f1024Alpha ^ 5 := by
    simpa using alpha_pow_ten_add 2
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_13 :
    polynomialEval (alphaReduction 13) = f1024Alpha ^ 13 := by
  have hrow : alphaReduction (13 : Fin 19) =
      Pi.single (3 : Fin 10) 1 + Pi.single (6 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 13 = f1024Alpha ^ 3 + f1024Alpha ^ 6 := by
    simpa using alpha_pow_ten_add 3
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_14 :
    polynomialEval (alphaReduction 14) = f1024Alpha ^ 14 := by
  have hrow : alphaReduction (14 : Fin 19) =
      Pi.single (4 : Fin 10) 1 + Pi.single (7 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 14 = f1024Alpha ^ 4 + f1024Alpha ^ 7 := by
    simpa using alpha_pow_ten_add 4
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_15 :
    polynomialEval (alphaReduction 15) = f1024Alpha ^ 15 := by
  have hrow : alphaReduction (15 : Fin 19) =
      Pi.single (5 : Fin 10) 1 + Pi.single (8 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 15 = f1024Alpha ^ 5 + f1024Alpha ^ 8 := by
    simpa using alpha_pow_ten_add 5
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_16 :
    polynomialEval (alphaReduction 16) = f1024Alpha ^ 16 := by
  have hrow : alphaReduction (16 : Fin 19) =
      Pi.single (6 : Fin 10) 1 + Pi.single (9 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 16 = f1024Alpha ^ 6 + f1024Alpha ^ 9 := by
    simpa using alpha_pow_ten_add 6
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_17 :
    polynomialEval (alphaReduction 17) = f1024Alpha ^ 17 := by
  have hrow : alphaReduction (17 : Fin 19) =
      Pi.single (0 : Fin 10) 1 + Pi.single (3 : Fin 10) 1 +
        Pi.single (7 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 17 = 1 + f1024Alpha ^ 3 + f1024Alpha ^ 7 := by
    calc
      f1024Alpha ^ 17 = f1024Alpha ^ 7 + f1024Alpha ^ 10 := by
        simpa using alpha_pow_ten_add 7
      _ = 1 + f1024Alpha ^ 3 + f1024Alpha ^ 7 := by
        rw [f1024Alpha_pow_ten]
        ring
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm

private theorem alphaReduction_eval_18 :
    polynomialEval (alphaReduction 18) = f1024Alpha ^ 18 := by
  have hrow : alphaReduction (18 : Fin 19) =
      Pi.single (1 : Fin 10) 1 + Pi.single (4 : Fin 10) 1 +
        Pi.single (8 : Fin 10) 1 := by decide
  have h11 : f1024Alpha ^ 11 = f1024Alpha + f1024Alpha ^ 4 := by
    simpa using alpha_pow_ten_add 1
  have hpower : f1024Alpha ^ 18 =
      f1024Alpha + f1024Alpha ^ 4 + f1024Alpha ^ 8 := by
    calc
      f1024Alpha ^ 18 = f1024Alpha ^ 8 + f1024Alpha ^ 11 := by
        simpa using alpha_pow_ten_add 8
      _ = f1024Alpha + f1024Alpha ^ 4 + f1024Alpha ^ 8 := by
        rw [h11]
        ring
  simpa [hrow, polynomialEval_single] using hpower.symm

/-- Every row of the fixed reduction table evaluates to its represented
power of `f1024Alpha`. -/
theorem alphaReduction_eval (power : Fin 19) :
    polynomialEval (alphaReduction power) = f1024Alpha ^ (power : Nat) := by
  fin_cases power
  · exact alphaReduction_eval_0
  · exact alphaReduction_eval_1
  · exact alphaReduction_eval_2
  · exact alphaReduction_eval_3
  · exact alphaReduction_eval_4
  · exact alphaReduction_eval_5
  · exact alphaReduction_eval_6
  · exact alphaReduction_eval_7
  · exact alphaReduction_eval_8
  · exact alphaReduction_eval_9
  · exact alphaReduction_eval_10
  · exact alphaReduction_eval_11
  · exact alphaReduction_eval_12
  · exact alphaReduction_eval_13
  · exact alphaReduction_eval_14
  · exact alphaReduction_eval_15
  · exact alphaReduction_eval_16
  · exact alphaReduction_eval_17
  · exact alphaReduction_eval_18

theorem wordMul_eq_sum (left right : Word) :
    wordMul left right =
      ∑ first : Fin 10, ∑ second : Fin 10,
        (left first * right second) •
          alphaReduction
            ⟨(first : Nat) + (second : Nat), by omega⟩ := by
  funext coordinate
  simp only [wordMul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The coordinate multiplication table implements multiplication in
`F1024`. -/
theorem polynomialEval_wordMul (left right : Word) :
    polynomialEval (wordMul left right) =
      polynomialEval left * polynomialEval right := by
  calc
    polynomialEval (wordMul left right) =
        ∑ first : Fin 10, ∑ second : Fin 10,
          (left first * right second) •
            f1024Alpha ^ ((first : Nat) + (second : Nat)) := by
              rw [wordMul_eq_sum]
              simp only [map_sum, map_smul, alphaReduction_eval]
    _ = (∑ first : Fin 10, left first • f1024Alpha ^ (first : Nat)) *
          ∑ second : Fin 10, right second • f1024Alpha ^ (second : Nat) := by
            rw [Fintype.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro first _
            apply Finset.sum_congr rfl
            intro second _
            simp only [Algebra.smul_def, map_mul]
            rw [pow_add]
            ring
    _ = polynomialEval left * polynomialEval right := rfl

/-- A selected-basis coordinate column evaluates to the corresponding actual
self-dual basis element. -/
theorem polynomialEval_selectedBasisWord (selected : Fin 10) :
    polynomialEval (selectedBasisWord selected) =
      f1024SelectedSelfDualBasis selected := by
  rw [f1024SelectedSelfDualBasis_apply]
  change
    (∑ power : Fin 10,
      selectedBasisWord selected power • f1024Alpha ^ (power : Nat)) =
      (f1024PolynomialBasis ᵥ*
        f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) selected
  simp only [selectedBasisWord, Matrix.vecMul, dotProduct,
    Matrix.map_apply, f1024PolynomialBasis_apply, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro power _
  rw [mul_comm]

theorem polynomialEval_selectedBasisSquareWord (selected : Fin 10) :
    polynomialEval (selectedBasisSquareWord selected) =
      f1024SelectedSelfDualBasis selected ^ 2 := by
  rw [selectedBasisSquareWord, polynomialEval_wordMul,
    polynomialEval_selectedBasisWord]
  rw [pow_two]

theorem polynomialEval_selectedBasisFourthWord (selected : Fin 10) :
    polynomialEval (selectedBasisFourthWord selected) =
      f1024SelectedSelfDualBasis selected ^ 4 := by
  rw [selectedBasisFourthWord, polynomialEval_wordMul,
    polynomialEval_selectedBasisSquareWord]
  ring

end QEC.Coding.Why24AppendixANF
