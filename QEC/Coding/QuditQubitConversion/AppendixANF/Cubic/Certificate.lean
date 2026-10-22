import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part00
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part01
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part02
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part03
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part04
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part05
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part06
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part07
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part08
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part09
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part10
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part11
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part12
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part13
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part14
import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Part15

/-!
# Composed cubic WHY24 Appendix-A ANF certificate

The imported blocks separately certify all 120 normalized cubic coefficients.
This module combines their fixed-pair interfaces without re-evaluating any
coefficient or Boolean input word.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

/-- Cubic coefficient certificate with fixed first index 0. -/
theorem sourceCoefficient_triple_first_0 (second third : Fin 10)
    (hfirst : (0 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 0 second third = cubicGateCoefficient 0 second third := by
  fin_cases second
  · change (0 : Nat) < 0 at hfirst
    omega
  · exact sourceCoefficient_triple_0_1 third hsecond
  · exact sourceCoefficient_triple_0_2 third hsecond
  · exact sourceCoefficient_triple_0_3 third hsecond
  · exact sourceCoefficient_triple_0_4 third hsecond
  · exact sourceCoefficient_triple_0_5 third hsecond
  · exact sourceCoefficient_triple_0_6 third hsecond
  · exact sourceCoefficient_triple_0_7 third hsecond
  · exact sourceCoefficient_triple_0_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 1. -/
theorem sourceCoefficient_triple_first_1 (second third : Fin 10)
    (hfirst : (1 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 1 second third = cubicGateCoefficient 1 second third := by
  fin_cases second
  · change (1 : Nat) < 0 at hfirst
    omega
  · change (1 : Nat) < 1 at hfirst
    omega
  · exact sourceCoefficient_triple_1_2 third hsecond
  · exact sourceCoefficient_triple_1_3 third hsecond
  · exact sourceCoefficient_triple_1_4 third hsecond
  · exact sourceCoefficient_triple_1_5 third hsecond
  · exact sourceCoefficient_triple_1_6 third hsecond
  · exact sourceCoefficient_triple_1_7 third hsecond
  · exact sourceCoefficient_triple_1_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 2. -/
theorem sourceCoefficient_triple_first_2 (second third : Fin 10)
    (hfirst : (2 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 2 second third = cubicGateCoefficient 2 second third := by
  fin_cases second
  · change (2 : Nat) < 0 at hfirst
    omega
  · change (2 : Nat) < 1 at hfirst
    omega
  · change (2 : Nat) < 2 at hfirst
    omega
  · exact sourceCoefficient_triple_2_3 third hsecond
  · exact sourceCoefficient_triple_2_4 third hsecond
  · exact sourceCoefficient_triple_2_5 third hsecond
  · exact sourceCoefficient_triple_2_6 third hsecond
  · exact sourceCoefficient_triple_2_7 third hsecond
  · exact sourceCoefficient_triple_2_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 3. -/
theorem sourceCoefficient_triple_first_3 (second third : Fin 10)
    (hfirst : (3 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 3 second third = cubicGateCoefficient 3 second third := by
  fin_cases second
  · change (3 : Nat) < 0 at hfirst
    omega
  · change (3 : Nat) < 1 at hfirst
    omega
  · change (3 : Nat) < 2 at hfirst
    omega
  · change (3 : Nat) < 3 at hfirst
    omega
  · exact sourceCoefficient_triple_3_4 third hsecond
  · exact sourceCoefficient_triple_3_5 third hsecond
  · exact sourceCoefficient_triple_3_6 third hsecond
  · exact sourceCoefficient_triple_3_7 third hsecond
  · exact sourceCoefficient_triple_3_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 4. -/
theorem sourceCoefficient_triple_first_4 (second third : Fin 10)
    (hfirst : (4 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 4 second third = cubicGateCoefficient 4 second third := by
  fin_cases second
  · change (4 : Nat) < 0 at hfirst
    omega
  · change (4 : Nat) < 1 at hfirst
    omega
  · change (4 : Nat) < 2 at hfirst
    omega
  · change (4 : Nat) < 3 at hfirst
    omega
  · change (4 : Nat) < 4 at hfirst
    omega
  · exact sourceCoefficient_triple_4_5 third hsecond
  · exact sourceCoefficient_triple_4_6 third hsecond
  · exact sourceCoefficient_triple_4_7 third hsecond
  · exact sourceCoefficient_triple_4_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 5. -/
theorem sourceCoefficient_triple_first_5 (second third : Fin 10)
    (hfirst : (5 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 5 second third = cubicGateCoefficient 5 second third := by
  fin_cases second
  · change (5 : Nat) < 0 at hfirst
    omega
  · change (5 : Nat) < 1 at hfirst
    omega
  · change (5 : Nat) < 2 at hfirst
    omega
  · change (5 : Nat) < 3 at hfirst
    omega
  · change (5 : Nat) < 4 at hfirst
    omega
  · change (5 : Nat) < 5 at hfirst
    omega
  · exact sourceCoefficient_triple_5_6 third hsecond
  · exact sourceCoefficient_triple_5_7 third hsecond
  · exact sourceCoefficient_triple_5_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 6. -/
theorem sourceCoefficient_triple_first_6 (second third : Fin 10)
    (hfirst : (6 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 6 second third = cubicGateCoefficient 6 second third := by
  fin_cases second
  · change (6 : Nat) < 0 at hfirst
    omega
  · change (6 : Nat) < 1 at hfirst
    omega
  · change (6 : Nat) < 2 at hfirst
    omega
  · change (6 : Nat) < 3 at hfirst
    omega
  · change (6 : Nat) < 4 at hfirst
    omega
  · change (6 : Nat) < 5 at hfirst
    omega
  · change (6 : Nat) < 6 at hfirst
    omega
  · exact sourceCoefficient_triple_6_7 third hsecond
  · exact sourceCoefficient_triple_6_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Cubic coefficient certificate with fixed first index 7. -/
theorem sourceCoefficient_triple_first_7 (second third : Fin 10)
    (hfirst : (7 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 7 second third = cubicGateCoefficient 7 second third := by
  fin_cases second
  · change (7 : Nat) < 0 at hfirst
    omega
  · change (7 : Nat) < 1 at hfirst
    omega
  · change (7 : Nat) < 2 at hfirst
    omega
  · change (7 : Nat) < 3 at hfirst
    omega
  · change (7 : Nat) < 4 at hfirst
    omega
  · change (7 : Nat) < 5 at hfirst
    omega
  · change (7 : Nat) < 6 at hfirst
    omega
  · change (7 : Nat) < 7 at hfirst
    omega
  · exact sourceCoefficient_triple_7_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega

/-- Every normalized increasing cubic source coefficient equals the literal
Appendix-A gate-list coefficient. -/
theorem sourceCoefficient_triple (first second third : Fin 10)
    (hfirst : first < second) (hsecond : second < third) :
    sourceTripleCoefficient first second third =
      cubicGateCoefficient first second third := by
  fin_cases first
  · exact sourceCoefficient_triple_first_0 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_1 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_2 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_3 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_4 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_5 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_6 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_7 second third hfirst hsecond
  · change (8 : Nat) < second.val at hfirst
    change second.val < third.val at hsecond
    omega
  · change (9 : Nat) < second.val at hfirst
    change second.val < third.val at hsecond
    omega

end QEC.Coding.Why24AppendixANF
