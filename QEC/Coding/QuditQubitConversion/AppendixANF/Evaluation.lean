import QEC.Coding.QuditQubitConversion.AppendixANF.Field

/-!
# Evaluation semantics for the WHY24 Appendix-A sparse ANF

The sparse source polynomial is evaluated compositionally.  Selected-basis
reconstruction, Frobenius linearity in characteristic two, and trace
linearity identify its value with the concrete seventh-power trace.  No
finite truth table or Boolean-word case split is used.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open Why24BooleanANF

theorem evaluate_linearANFWord (word : Word) (basisWords : Fin 10 → Word)
    (power : Fin 10) :
    evaluate word (linearANFWord basisWords power) =
      ∑ selected : Fin 10, basisWords selected power * word selected := by
  rw [linearANFWord, map_sum]
  apply Finset.sum_congr rfl
  intro selected _
  simp only [map_smul, evaluate_generator, smul_eq_mul]

theorem polynomialEval_evaluate_linearANFWord
    (word : Word) (basisWords : Fin 10 → Word) :
    polynomialEval
        (fun power => evaluate word (linearANFWord basisWords power)) =
      ∑ selected : Fin 10, word selected • polynomialEval (basisWords selected) := by
  have hcoordinates :
      (fun power => evaluate word (linearANFWord basisWords power)) =
        ∑ selected : Fin 10, word selected • basisWords selected := by
    funext power
    rw [evaluate_linearANFWord]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro selected _
    rw [mul_comm]
  rw [hcoordinates, map_sum]
  simp only [map_smul]

theorem selectedCoordinates_symm_eq_sum (word : Word) :
    f1024SelectedCoordinates.symm word =
      ∑ selected : Fin 10,
        word selected • f1024SelectedSelfDualBasis selected := by
  rw [f1024SelectedCoordinates, Module.Basis.equivFun_symm_apply]

private theorem bit_smul_square (bit : ZMod 2) (value : F1024) :
    (bit • value) ^ 2 = bit • value ^ 2 := by
  simp only [Algebra.smul_def, mul_pow, ← map_pow]
  rw [ZMod.pow_card]

private theorem sum_bit_smul_square (word : Word) (values : Fin 10 → F1024) :
    (∑ selected : Fin 10, word selected • values selected) ^ 2 =
      ∑ selected : Fin 10, word selected • values selected ^ 2 := by
  calc
    (∑ selected : Fin 10, word selected • values selected) ^ 2 =
        ∑ selected : Fin 10, (word selected • values selected) ^ 2 := by
          simpa using
            (sum_pow_char (R := F1024) (p := 2)
              (Finset.univ : Finset (Fin 10))
              (fun selected => word selected • values selected))
    _ = ∑ selected : Fin 10, word selected • values selected ^ 2 := by
      apply Finset.sum_congr rfl
      intro selected _
      exact bit_smul_square (word selected) (values selected)

theorem polynomialEval_evaluate_selectedANFWord (word : Word) :
    polynomialEval (fun power => evaluate word (selectedANFWord power)) =
      f1024SelectedCoordinates.symm word := by
  rw [selectedANFWord, polynomialEval_evaluate_linearANFWord]
  simp_rw [polynomialEval_selectedBasisWord]
  exact (selectedCoordinates_symm_eq_sum word).symm

theorem polynomialEval_evaluate_selectedSquareANFWord (word : Word) :
    polynomialEval (fun power => evaluate word (selectedSquareANFWord power)) =
      (f1024SelectedCoordinates.symm word) ^ 2 := by
  rw [selectedSquareANFWord, polynomialEval_evaluate_linearANFWord]
  simp_rw [polynomialEval_selectedBasisSquareWord]
  rw [← sum_bit_smul_square, ← selectedCoordinates_symm_eq_sum]

theorem polynomialEval_evaluate_selectedFourthANFWord (word : Word) :
    polynomialEval (fun power => evaluate word (selectedFourthANFWord power)) =
      (f1024SelectedCoordinates.symm word) ^ 4 := by
  rw [selectedFourthANFWord, polynomialEval_evaluate_linearANFWord]
  simp_rw [polynomialEval_selectedBasisFourthWord]
  calc
    (∑ selected : Fin 10,
        word selected • f1024SelectedSelfDualBasis selected ^ 4) =
        (∑ selected : Fin 10,
          word selected • f1024SelectedSelfDualBasis selected ^ 2) ^ 2 := by
            rw [sum_bit_smul_square]
            apply Finset.sum_congr rfl
            intro selected _
            congr 1
            ring
    _ = ((∑ selected : Fin 10,
          word selected • f1024SelectedSelfDualBasis selected) ^ 2) ^ 2 := by
            congr 1
            exact (sum_bit_smul_square word
              (fun selected => f1024SelectedSelfDualBasis selected)).symm
    _ = (f1024SelectedCoordinates.symm word) ^ 4 := by
      rw [← selectedCoordinates_symm_eq_sum]
      ring

private theorem trace_alpha_pow (power : Fin 10) :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ (power : Nat)) =
      f1024PolynomialTraceGram power 0 := by
  have hentry := congr_fun (congr_fun f1024PolynomialTraceMatrix_eq power) 0
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f1024PolynomialBasis_apply] using hentry

theorem trace_polynomialEval_eq_seven (coordinates : Word) :
    Algebra.trace (ZMod 2) F1024 (polynomialEval coordinates) = coordinates 7 := by
  change
    Algebra.trace (ZMod 2) F1024
        (∑ power : Fin 10, coordinates power • f1024Alpha ^ (power : Nat)) =
      coordinates 7
  rw [map_sum]
  simp_rw [(Algebra.trace (ZMod 2) F1024).map_smul, trace_alpha_pow]
  rw [Fintype.sum_eq_single (7 : Fin 10)]
  · simp [f1024PolynomialTraceGram]
  · intro power hpower
    fin_cases power <;> simp_all [f1024PolynomialTraceGram]

theorem traceTensor_eq_trace (first second third : Fin 10) :
    traceTensor first second third =
      Algebra.trace (ZMod 2) F1024
        (f1024SelectedSelfDualBasis first *
          f1024SelectedSelfDualBasis second ^ 2 *
          f1024SelectedSelfDualBasis third ^ 4) := by
  have heval :
      polynomialEval
          (wordMul
            (wordMul (selectedBasisWord first) (selectedBasisSquareWord second))
            (selectedBasisFourthWord third)) =
        f1024SelectedSelfDualBasis first *
          f1024SelectedSelfDualBasis second ^ 2 *
          f1024SelectedSelfDualBasis third ^ 4 := by
    rw [polynomialEval_wordMul, polynomialEval_wordMul,
      polynomialEval_selectedBasisWord,
      polynomialEval_selectedBasisSquareWord,
      polynomialEval_selectedBasisFourthWord]
  have htrace := congrArg (Algebra.trace (ZMod 2) F1024) heval
  rw [trace_polynomialEval_eq_seven] at htrace
  simpa only [traceTensor] using htrace

private theorem trace_selected_triple_sums (word : Word) :
    Algebra.trace (ZMod 2) F1024
        ((∑ first : Fin 10,
            word first • f1024SelectedSelfDualBasis first) *
          (∑ second : Fin 10,
            word second • f1024SelectedSelfDualBasis second ^ 2) *
          (∑ third : Fin 10,
            word third • f1024SelectedSelfDualBasis third ^ 4)) =
      ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        (word first * word second * word third) *
          Algebra.trace (ZMod 2) F1024
            (f1024SelectedSelfDualBasis first *
              f1024SelectedSelfDualBasis second ^ 2 *
              f1024SelectedSelfDualBasis third ^ 4) := by
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  have hterm :
      (word first • f1024SelectedSelfDualBasis first) *
          (word second • f1024SelectedSelfDualBasis second ^ 2) *
          (word third • f1024SelectedSelfDualBasis third ^ 4) =
        (word first * word second * word third) •
          (f1024SelectedSelfDualBasis first *
            f1024SelectedSelfDualBasis second ^ 2 *
            f1024SelectedSelfDualBasis third ^ 4) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [hterm, (Algebra.trace (ZMod 2) F1024).map_smul]
  simp only [smul_eq_mul]

/-- Evaluating the sparse source ANF on any Boolean word gives the actual
seventh-power trace of the corresponding selected-basis field element. -/
theorem evaluate_sourcePhasePolynomial (word : Word) :
    evaluate word sourcePhasePolynomial =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by
  have hevaluate :
      evaluate word sourcePhasePolynomial =
        ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
          (word first * word second * word third) *
            Algebra.trace (ZMod 2) F1024
              (f1024SelectedSelfDualBasis first *
                f1024SelectedSelfDualBasis second ^ 2 *
                f1024SelectedSelfDualBasis third ^ 4) := by
    rw [sourcePhasePolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro third _
    simp only [map_smul, map_mul, evaluate_generator, smul_eq_mul]
    rw [traceTensor_eq_trace]
    ring
  rw [hevaluate, ← trace_selected_triple_sums,
    ← selectedCoordinates_symm_eq_sum]
  have hsquare := polynomialEval_evaluate_selectedSquareANFWord word
  have hfourth := polynomialEval_evaluate_selectedFourthANFWord word
  rw [selectedSquareANFWord, polynomialEval_evaluate_linearANFWord] at hsquare
  rw [selectedFourthANFWord, polynomialEval_evaluate_linearANFWord] at hfourth
  simp_rw [polynomialEval_selectedBasisSquareWord] at hsquare
  simp_rw [polynomialEval_selectedBasisFourthWord] at hfourth
  rw [hsquare, hfourth]
  congr 1
  ring

end QEC.Coding.Why24AppendixANF
