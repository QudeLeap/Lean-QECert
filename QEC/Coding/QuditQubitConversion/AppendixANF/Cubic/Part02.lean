import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 02 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_4 :
    sourceTripleCoefficient 0 3 4 = cubicGateCoefficient 0 3 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_5 :
    sourceTripleCoefficient 0 3 5 = cubicGateCoefficient 0 3 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_6 :
    sourceTripleCoefficient 0 3 6 = cubicGateCoefficient 0 3 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_7 :
    sourceTripleCoefficient 0 3 7 = cubicGateCoefficient 0 3 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_8 :
    sourceTripleCoefficient 0 3 8 = cubicGateCoefficient 0 3 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_3_9 :
    sourceTripleCoefficient 0 3 9 = cubicGateCoefficient 0 3 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 0, 3. -/
theorem sourceCoefficient_triple_0_3 (third : Fin 10)
    (hlt : (3 : Fin 10) < third) :
    sourceTripleCoefficient 0 3 third = cubicGateCoefficient 0 3 third := by
  fin_cases third
  · change (3 : Nat) < 0 at hlt
    omega
  · change (3 : Nat) < 1 at hlt
    omega
  · change (3 : Nat) < 2 at hlt
    omega
  · change (3 : Nat) < 3 at hlt
    omega
  · exact sourceCoefficient_triple_0_3_4
  · exact sourceCoefficient_triple_0_3_5
  · exact sourceCoefficient_triple_0_3_6
  · exact sourceCoefficient_triple_0_3_7
  · exact sourceCoefficient_triple_0_3_8
  · exact sourceCoefficient_triple_0_3_9

end QEC.Coding.Why24AppendixANF
