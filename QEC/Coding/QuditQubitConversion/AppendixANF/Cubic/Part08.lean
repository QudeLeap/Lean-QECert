import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 08 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_6_7 :
    sourceTripleCoefficient 1 6 7 = cubicGateCoefficient 1 6 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_6_8 :
    sourceTripleCoefficient 1 6 8 = cubicGateCoefficient 1 6 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_6_9 :
    sourceTripleCoefficient 1 6 9 = cubicGateCoefficient 1 6 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 6. -/
theorem sourceCoefficient_triple_1_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 1 6 third = cubicGateCoefficient 1 6 third := by
  fin_cases third
  · change (6 : Nat) < 0 at hlt
    omega
  · change (6 : Nat) < 1 at hlt
    omega
  · change (6 : Nat) < 2 at hlt
    omega
  · change (6 : Nat) < 3 at hlt
    omega
  · change (6 : Nat) < 4 at hlt
    omega
  · change (6 : Nat) < 5 at hlt
    omega
  · change (6 : Nat) < 6 at hlt
    omega
  · exact sourceCoefficient_triple_1_6_7
  · exact sourceCoefficient_triple_1_6_8
  · exact sourceCoefficient_triple_1_6_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_7_8 :
    sourceTripleCoefficient 1 7 8 = cubicGateCoefficient 1 7 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_7_9 :
    sourceTripleCoefficient 1 7 9 = cubicGateCoefficient 1 7 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 7. -/
theorem sourceCoefficient_triple_1_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 1 7 third = cubicGateCoefficient 1 7 third := by
  fin_cases third
  · change (7 : Nat) < 0 at hlt
    omega
  · change (7 : Nat) < 1 at hlt
    omega
  · change (7 : Nat) < 2 at hlt
    omega
  · change (7 : Nat) < 3 at hlt
    omega
  · change (7 : Nat) < 4 at hlt
    omega
  · change (7 : Nat) < 5 at hlt
    omega
  · change (7 : Nat) < 6 at hlt
    omega
  · change (7 : Nat) < 7 at hlt
    omega
  · exact sourceCoefficient_triple_1_7_8
  · exact sourceCoefficient_triple_1_7_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_8_9 :
    sourceTripleCoefficient 1 8 9 = cubicGateCoefficient 1 8 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 8. -/
theorem sourceCoefficient_triple_1_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 1 8 third = cubicGateCoefficient 1 8 third := by
  fin_cases third
  · change (8 : Nat) < 0 at hlt
    omega
  · change (8 : Nat) < 1 at hlt
    omega
  · change (8 : Nat) < 2 at hlt
    omega
  · change (8 : Nat) < 3 at hlt
    omega
  · change (8 : Nat) < 4 at hlt
    omega
  · change (8 : Nat) < 5 at hlt
    omega
  · change (8 : Nat) < 6 at hlt
    omega
  · change (8 : Nat) < 7 at hlt
    omega
  · change (8 : Nat) < 8 at hlt
    omega
  · exact sourceCoefficient_triple_1_8_9

end QEC.Coding.Why24AppendixANF
