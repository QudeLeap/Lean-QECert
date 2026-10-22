import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.PartA
import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.PartB
import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.PartC
import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.PartD

/-!
# Composed quadratic WHY24 Appendix-A ANF certificate

The four imported blocks separately certify all 45 normalized quadratic
coefficients.  This module combines their fixed-left interfaces without
re-evaluating any coefficient or Boolean input word.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

/-- Every normalized quadratic source coefficient equals the literal gate-list
coefficient. -/
theorem sourceCoefficient_pair (left right : Fin 10) (hlt : left < right) :
    sourcePairCoefficient left right = quadraticGateCoefficient left right := by
  fin_cases left
  · exact sourceCoefficient_pair_left_0 right hlt
  · exact sourceCoefficient_pair_left_1 right hlt
  · exact sourceCoefficient_pair_left_2 right hlt
  · exact sourceCoefficient_pair_left_3 right hlt
  · exact sourceCoefficient_pair_left_4 right hlt
  · exact sourceCoefficient_pair_left_5 right hlt
  · exact sourceCoefficient_pair_left_6 right hlt
  · exact sourceCoefficient_pair_left_7 right hlt
  · exact sourceCoefficient_pair_left_8 right hlt
  · change (9 : Nat) < right.val at hlt
    omega

end QEC.Coding.Why24AppendixANF
