import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 01 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_3 :
    sourceTripleCoefficient 0 2 3 = cubicGateCoefficient 0 2 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_4 :
    sourceTripleCoefficient 0 2 4 = cubicGateCoefficient 0 2 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_5 :
    sourceTripleCoefficient 0 2 5 = cubicGateCoefficient 0 2 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_6 :
    sourceTripleCoefficient 0 2 6 = cubicGateCoefficient 0 2 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_7 :
    sourceTripleCoefficient 0 2 7 = cubicGateCoefficient 0 2 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_8 :
    sourceTripleCoefficient 0 2 8 = cubicGateCoefficient 0 2 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_2_9 :
    sourceTripleCoefficient 0 2 9 = cubicGateCoefficient 0 2 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 0, 2. -/
theorem sourceCoefficient_triple_0_2 (third : Fin 10)
    (hlt : (2 : Fin 10) < third) :
    sourceTripleCoefficient 0 2 third = cubicGateCoefficient 0 2 third := by
  fin_cases third
  · change (2 : Nat) < 0 at hlt
    omega
  · change (2 : Nat) < 1 at hlt
    omega
  · change (2 : Nat) < 2 at hlt
    omega
  · exact sourceCoefficient_triple_0_2_3
  · exact sourceCoefficient_triple_0_2_4
  · exact sourceCoefficient_triple_0_2_5
  · exact sourceCoefficient_triple_0_2_6
  · exact sourceCoefficient_triple_0_2_7
  · exact sourceCoefficient_triple_0_2_8
  · exact sourceCoefficient_triple_0_2_9

end QEC.Coding.Why24AppendixANF
