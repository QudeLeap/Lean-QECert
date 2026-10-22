import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.Data

/-!
# Quadratic WHY24 ANF coefficient block A

This module contains 9 independent normalized coefficient certificates.
It imports the compiled source tensor and contains no Boolean-input enumeration.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_1 :
    sourcePairCoefficient 0 1 = quadraticGateCoefficient 0 1 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_2 :
    sourcePairCoefficient 0 2 = quadraticGateCoefficient 0 2 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_3 :
    sourcePairCoefficient 0 3 = quadraticGateCoefficient 0 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_4 :
    sourcePairCoefficient 0 4 = quadraticGateCoefficient 0 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_5 :
    sourcePairCoefficient 0 5 = quadraticGateCoefficient 0 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_6 :
    sourcePairCoefficient 0 6 = quadraticGateCoefficient 0 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_7 :
    sourcePairCoefficient 0 7 = quadraticGateCoefficient 0 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_8 :
    sourcePairCoefficient 0 8 = quadraticGateCoefficient 0 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_0_9 :
    sourcePairCoefficient 0 9 = quadraticGateCoefficient 0 9 := by
  decide

/-- Quadratic coefficient certificate with fixed first index 0. -/
theorem sourceCoefficient_pair_left_0 (right : Fin 10)
    (hlt : (0 : Fin 10) < right) :
    sourcePairCoefficient 0 right = quadraticGateCoefficient 0 right := by
  fin_cases right
  · change (0 : Nat) < 0 at hlt
    omega
  · exact sourceCoefficient_pair_0_1
  · exact sourceCoefficient_pair_0_2
  · exact sourceCoefficient_pair_0_3
  · exact sourceCoefficient_pair_0_4
  · exact sourceCoefficient_pair_0_5
  · exact sourceCoefficient_pair_0_6
  · exact sourceCoefficient_pair_0_7
  · exact sourceCoefficient_pair_0_8
  · exact sourceCoefficient_pair_0_9

end QEC.Coding.Why24AppendixANF
