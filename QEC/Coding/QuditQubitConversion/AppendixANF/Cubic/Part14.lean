import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 14 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_5_6 :
    sourceTripleCoefficient 4 5 6 = cubicGateCoefficient 4 5 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_5_7 :
    sourceTripleCoefficient 4 5 7 = cubicGateCoefficient 4 5 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_5_8 :
    sourceTripleCoefficient 4 5 8 = cubicGateCoefficient 4 5 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_5_9 :
    sourceTripleCoefficient 4 5 9 = cubicGateCoefficient 4 5 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 4, 5. -/
theorem sourceCoefficient_triple_4_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 4 5 third = cubicGateCoefficient 4 5 third := by
  fin_cases third
  · change (5 : Nat) < 0 at hlt
    omega
  · change (5 : Nat) < 1 at hlt
    omega
  · change (5 : Nat) < 2 at hlt
    omega
  · change (5 : Nat) < 3 at hlt
    omega
  · change (5 : Nat) < 4 at hlt
    omega
  · change (5 : Nat) < 5 at hlt
    omega
  · exact sourceCoefficient_triple_4_5_6
  · exact sourceCoefficient_triple_4_5_7
  · exact sourceCoefficient_triple_4_5_8
  · exact sourceCoefficient_triple_4_5_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_6_7 :
    sourceTripleCoefficient 4 6 7 = cubicGateCoefficient 4 6 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_6_8 :
    sourceTripleCoefficient 4 6 8 = cubicGateCoefficient 4 6 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_6_9 :
    sourceTripleCoefficient 4 6 9 = cubicGateCoefficient 4 6 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 4, 6. -/
theorem sourceCoefficient_triple_4_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 4 6 third = cubicGateCoefficient 4 6 third := by
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
  · exact sourceCoefficient_triple_4_6_7
  · exact sourceCoefficient_triple_4_6_8
  · exact sourceCoefficient_triple_4_6_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_7_8 :
    sourceTripleCoefficient 4 7 8 = cubicGateCoefficient 4 7 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_7_9 :
    sourceTripleCoefficient 4 7 9 = cubicGateCoefficient 4 7 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 4, 7. -/
theorem sourceCoefficient_triple_4_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 4 7 third = cubicGateCoefficient 4 7 third := by
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
  · exact sourceCoefficient_triple_4_7_8
  · exact sourceCoefficient_triple_4_7_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_4_8_9 :
    sourceTripleCoefficient 4 8 9 = cubicGateCoefficient 4 8 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 4, 8. -/
theorem sourceCoefficient_triple_4_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 4 8 third = cubicGateCoefficient 4 8 third := by
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
  · exact sourceCoefficient_triple_4_8_9

end QEC.Coding.Why24AppendixANF
