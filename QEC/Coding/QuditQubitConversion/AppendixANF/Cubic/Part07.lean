import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 07 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_4_5 :
    sourceTripleCoefficient 1 4 5 = cubicGateCoefficient 1 4 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_4_6 :
    sourceTripleCoefficient 1 4 6 = cubicGateCoefficient 1 4 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_4_7 :
    sourceTripleCoefficient 1 4 7 = cubicGateCoefficient 1 4 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_4_8 :
    sourceTripleCoefficient 1 4 8 = cubicGateCoefficient 1 4 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_4_9 :
    sourceTripleCoefficient 1 4 9 = cubicGateCoefficient 1 4 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 4. -/
theorem sourceCoefficient_triple_1_4 (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 1 4 third = cubicGateCoefficient 1 4 third := by
  fin_cases third
  · change (4 : Nat) < 0 at hlt
    omega
  · change (4 : Nat) < 1 at hlt
    omega
  · change (4 : Nat) < 2 at hlt
    omega
  · change (4 : Nat) < 3 at hlt
    omega
  · change (4 : Nat) < 4 at hlt
    omega
  · exact sourceCoefficient_triple_1_4_5
  · exact sourceCoefficient_triple_1_4_6
  · exact sourceCoefficient_triple_1_4_7
  · exact sourceCoefficient_triple_1_4_8
  · exact sourceCoefficient_triple_1_4_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_5_6 :
    sourceTripleCoefficient 1 5 6 = cubicGateCoefficient 1 5 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_5_7 :
    sourceTripleCoefficient 1 5 7 = cubicGateCoefficient 1 5 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_5_8 :
    sourceTripleCoefficient 1 5 8 = cubicGateCoefficient 1 5 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_5_9 :
    sourceTripleCoefficient 1 5 9 = cubicGateCoefficient 1 5 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 5. -/
theorem sourceCoefficient_triple_1_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 1 5 third = cubicGateCoefficient 1 5 third := by
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
  · exact sourceCoefficient_triple_1_5_6
  · exact sourceCoefficient_triple_1_5_7
  · exact sourceCoefficient_triple_1_5_8
  · exact sourceCoefficient_triple_1_5_9

end QEC.Coding.Why24AppendixANF
