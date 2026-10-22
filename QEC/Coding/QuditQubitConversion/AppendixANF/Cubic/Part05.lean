import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 05 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_3 :
    sourceTripleCoefficient 1 2 3 = cubicGateCoefficient 1 2 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_4 :
    sourceTripleCoefficient 1 2 4 = cubicGateCoefficient 1 2 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_5 :
    sourceTripleCoefficient 1 2 5 = cubicGateCoefficient 1 2 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_6 :
    sourceTripleCoefficient 1 2 6 = cubicGateCoefficient 1 2 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_7 :
    sourceTripleCoefficient 1 2 7 = cubicGateCoefficient 1 2 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_8 :
    sourceTripleCoefficient 1 2 8 = cubicGateCoefficient 1 2 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_1_2_9 :
    sourceTripleCoefficient 1 2 9 = cubicGateCoefficient 1 2 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 1, 2. -/
theorem sourceCoefficient_triple_1_2 (third : Fin 10)
    (hlt : (2 : Fin 10) < third) :
    sourceTripleCoefficient 1 2 third = cubicGateCoefficient 1 2 third := by
  fin_cases third
  · change (2 : Nat) < 0 at hlt
    omega
  · change (2 : Nat) < 1 at hlt
    omega
  · change (2 : Nat) < 2 at hlt
    omega
  · exact sourceCoefficient_triple_1_2_3
  · exact sourceCoefficient_triple_1_2_4
  · exact sourceCoefficient_triple_1_2_5
  · exact sourceCoefficient_triple_1_2_6
  · exact sourceCoefficient_triple_1_2_7
  · exact sourceCoefficient_triple_1_2_8
  · exact sourceCoefficient_triple_1_2_9

end QEC.Coding.Why24AppendixANF
