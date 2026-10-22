import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! Bounded cubic coefficient block 12 for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_4_5 :
    sourceTripleCoefficient 3 4 5 = cubicGateCoefficient 3 4 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_4_6 :
    sourceTripleCoefficient 3 4 6 = cubicGateCoefficient 3 4 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_4_7 :
    sourceTripleCoefficient 3 4 7 = cubicGateCoefficient 3 4 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_4_8 :
    sourceTripleCoefficient 3 4 8 = cubicGateCoefficient 3 4 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_4_9 :
    sourceTripleCoefficient 3 4 9 = cubicGateCoefficient 3 4 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 3, 4. -/
theorem sourceCoefficient_triple_3_4 (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 3 4 third = cubicGateCoefficient 3 4 third := by
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
  · exact sourceCoefficient_triple_3_4_5
  · exact sourceCoefficient_triple_3_4_6
  · exact sourceCoefficient_triple_3_4_7
  · exact sourceCoefficient_triple_3_4_8
  · exact sourceCoefficient_triple_3_4_9

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_5_6 :
    sourceTripleCoefficient 3 5 6 = cubicGateCoefficient 3 5 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_5_7 :
    sourceTripleCoefficient 3 5 7 = cubicGateCoefficient 3 5 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_5_8 :
    sourceTripleCoefficient 3 5 8 = cubicGateCoefficient 3 5 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_3_5_9 :
    sourceTripleCoefficient 3 5 9 = cubicGateCoefficient 3 5 9 := by
  decide

/-- Cubic coefficient certificate with fixed first indices 3, 5. -/
theorem sourceCoefficient_triple_3_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 3 5 third = cubicGateCoefficient 3 5 third := by
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
  · exact sourceCoefficient_triple_3_5_6
  · exact sourceCoefficient_triple_3_5_7
  · exact sourceCoefficient_triple_3_5_8
  · exact sourceCoefficient_triple_3_5_9

end QEC.Coding.Why24AppendixANF
