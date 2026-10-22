import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Probe

/-! Bounded cubic coefficient block 00 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_2 :
    sourceTripleCoefficient 0 1 2 = cubicGateCoefficient 0 1 2 := by
  exact sourceCoefficient_triple_0_1_2_probe

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_3 :
    sourceTripleCoefficient 0 1 3 = cubicGateCoefficient 0 1 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_4 :
    sourceTripleCoefficient 0 1 4 = cubicGateCoefficient 0 1 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_5 :
    sourceTripleCoefficient 0 1 5 = cubicGateCoefficient 0 1 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_6 :
    sourceTripleCoefficient 0 1 6 = cubicGateCoefficient 0 1 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_7 :
    sourceTripleCoefficient 0 1 7 = cubicGateCoefficient 0 1 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_8 :
    sourceTripleCoefficient 0 1 8 = cubicGateCoefficient 0 1 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_9 :
    sourceTripleCoefficient 0 1 9 = cubicGateCoefficient 0 1 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 0, 1. -/
theorem sourceCoefficient_triple_0_1 (third : Fin 10)
    (hlt : (1 : Fin 10) < third) :
    sourceTripleCoefficient 0 1 third = cubicGateCoefficient 0 1 third := by
  fin_cases third
  · change (1 : Nat) < 0 at hlt
    omega
  · change (1 : Nat) < 1 at hlt
    omega
  · exact sourceCoefficient_triple_0_1_2
  · exact sourceCoefficient_triple_0_1_3
  · exact sourceCoefficient_triple_0_1_4
  · exact sourceCoefficient_triple_0_1_5
  · exact sourceCoefficient_triple_0_1_6
  · exact sourceCoefficient_triple_0_1_7
  · exact sourceCoefficient_triple_0_1_8
  · exact sourceCoefficient_triple_0_1_9

end QEC.Coding.Why24AppendixANF
