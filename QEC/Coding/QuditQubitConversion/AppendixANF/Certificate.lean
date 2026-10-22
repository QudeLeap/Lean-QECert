import QEC.Coding.QuditQubitConversion.BooleanANF
import QEC.Coding.QuditQubitConversion.U7Gate

/-!
# Sparse ANF certificate for the WHY24 Appendix-A phase

This module computes the source phase as a cubic Boolean polynomial.  The
linear factors represent the selected-basis element and its second and fourth
Frobenius powers; their product therefore represents the seventh power.  All
coefficient computation stays in sparse squarefree ANF form.

The certificate is deliberately compiled separately from the Hilbert-space
resource circuit.  No theorem here enumerates the 1024 Boolean input words.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open Why24BooleanANF

abbrev Word := Fin 10 → ZMod 2
abbrev ANF := Why24BooleanANF.Polynomial 10
abbrev ANFWord := Fin 10 → ANF

/-- Polynomial-coordinate reductions of `α^r`, for `0 ≤ r ≤ 18`. -/
def alphaReduction : Matrix (Fin 19) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
     1, 0, 0, 1, 0, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 0, 0, 0, 1, 0]

/-- Multiplication of fixed polynomial-coordinate field words. -/
def wordMul (left right : Word) : Word :=
  fun coordinate =>
    ∑ first : Fin 10, ∑ second : Fin 10,
      (left first * right second) *
        alphaReduction
          ⟨(first : Nat) + (second : Nat), by omega⟩ coordinate

/-- Multiplication of polynomial-coordinate words with sparse ANF entries. -/
def anfWordMul (left right : ANFWord) : ANFWord :=
  fun coordinate =>
    ∑ first : Fin 10, ∑ second : Fin 10,
      alphaReduction
          ⟨(first : Nat) + (second : Nat), by omega⟩ coordinate •
        (left first * right second)

/-- The polynomial-coordinate word for one selected self-dual basis vector. -/
def selectedBasisWord (selected : Fin 10) : Word :=
  fun power => f1024SelectedSelfDualP power selected

/-- Polynomial coordinates of the square of one selected basis vector. -/
def selectedBasisSquareWord (selected : Fin 10) : Word :=
  wordMul (selectedBasisWord selected) (selectedBasisWord selected)

/-- Polynomial coordinates of the fourth power of one selected basis vector. -/
def selectedBasisFourthWord (selected : Fin 10) : Word :=
  wordMul (selectedBasisSquareWord selected) (selectedBasisSquareWord selected)

/-- Turn ten fixed coordinate words into one linear sparse-ANF coordinate word. -/
def linearANFWord (basisWords : Fin 10 → Word) : ANFWord :=
  fun power =>
    ∑ selected : Fin 10,
      basisWords selected power • generator selected

/-- The three Frobenius-linear factors whose product is the seventh power. -/
def selectedANFWord : ANFWord :=
  linearANFWord selectedBasisWord

def selectedSquareANFWord : ANFWord :=
  linearANFWord selectedBasisSquareWord

def selectedFourthANFWord : ANFWord :=
  linearANFWord selectedBasisFourthWord

/-- The trace tensor for the three Frobenius-linear factors `x`, `x²`, and
`x⁴`.  Coordinate seven is the trace coordinate in the polynomial basis. -/
def traceTensor (first second third : Fin 10) : ZMod 2 :=
  wordMul
    (wordMul (selectedBasisWord first) (selectedBasisSquareWord second))
    (selectedBasisFourthWord third) 7

/-- The normalized cubic ANF for the selected-basis seventh-power trace. -/
def sourcePhasePolynomial : ANF :=
  ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    traceTensor first second third •
      (generator first * generator second * generator third)

/-- The squarefree support produced by one ordered tensor entry. -/
def tripleSupport (first second third : Fin 10) : Finset (Fin 10) :=
  {first, second, third}

/-- A directly executable coefficient of the normalized cubic trace tensor.
For a support of size at most three, at most six tensor entries contribute. -/
def sourceCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if tripleSupport first second third = support then
      traceTensor first second third
    else 0

/-- Singleton monomial used for the first bounded source-coefficient probe. -/
def singletonMonomial (coordinate : Fin 10) : Monomial 10 :=
  ⟨{coordinate}⟩

private theorem sourceCoefficient_singleton_0 : sourceCoefficient {0} = 1 := by decide
private theorem sourceCoefficient_singleton_1 : sourceCoefficient {1} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_2 : sourceCoefficient {2} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_3 : sourceCoefficient {3} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_4 : sourceCoefficient {4} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_5 : sourceCoefficient {5} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_6 : sourceCoefficient {6} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_7 : sourceCoefficient {7} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_8 : sourceCoefficient {8} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_9 : sourceCoefficient {9} = 1 := by decide

/-- The ten linear WHY24 coefficients.  Each independent certificate reduces
one sparse coefficient of the compositional cubic construction. -/
theorem sourceCoefficient_singleton (coordinate : Fin 10) :
    sourceCoefficient {coordinate} = 1 := by
  fin_cases coordinate
  · exact sourceCoefficient_singleton_0
  · exact sourceCoefficient_singleton_1
  · exact sourceCoefficient_singleton_2
  · exact sourceCoefficient_singleton_3
  · exact sourceCoefficient_singleton_4
  · exact sourceCoefficient_singleton_5
  · exact sourceCoefficient_singleton_6
  · exact sourceCoefficient_singleton_7
  · exact sourceCoefficient_singleton_8
  · exact sourceCoefficient_singleton_9

end QEC.Coding.Why24AppendixANF
