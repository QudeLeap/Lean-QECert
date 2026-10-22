import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.Data

/-!
# Quadratic WHY24 ANF coefficient block B

This module contains 15 independent normalized coefficient certificates.
It imports the compiled source tensor and contains no Boolean-input enumeration.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_2 :
    sourcePairCoefficient 1 2 = quadraticGateCoefficient 1 2 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_3 :
    sourcePairCoefficient 1 3 = quadraticGateCoefficient 1 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_4 :
    sourcePairCoefficient 1 4 = quadraticGateCoefficient 1 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_5 :
    sourcePairCoefficient 1 5 = quadraticGateCoefficient 1 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_6 :
    sourcePairCoefficient 1 6 = quadraticGateCoefficient 1 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_7 :
    sourcePairCoefficient 1 7 = quadraticGateCoefficient 1 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_8 :
    sourcePairCoefficient 1 8 = quadraticGateCoefficient 1 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_1_9 :
    sourcePairCoefficient 1 9 = quadraticGateCoefficient 1 9 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_3 :
    sourcePairCoefficient 2 3 = quadraticGateCoefficient 2 3 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_4 :
    sourcePairCoefficient 2 4 = quadraticGateCoefficient 2 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_5 :
    sourcePairCoefficient 2 5 = quadraticGateCoefficient 2 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_6 :
    sourcePairCoefficient 2 6 = quadraticGateCoefficient 2 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_7 :
    sourcePairCoefficient 2 7 = quadraticGateCoefficient 2 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_8 :
    sourcePairCoefficient 2 8 = quadraticGateCoefficient 2 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_2_9 :
    sourcePairCoefficient 2 9 = quadraticGateCoefficient 2 9 := by
  decide

/-- Quadratic coefficient certificate with fixed first index 1. -/
theorem sourceCoefficient_pair_left_1 (right : Fin 10)
    (hlt : (1 : Fin 10) < right) :
    sourcePairCoefficient 1 right = quadraticGateCoefficient 1 right := by
  fin_cases right
  · change (1 : Nat) < 0 at hlt
    omega
  · change (1 : Nat) < 1 at hlt
    omega
  · exact sourceCoefficient_pair_1_2
  · exact sourceCoefficient_pair_1_3
  · exact sourceCoefficient_pair_1_4
  · exact sourceCoefficient_pair_1_5
  · exact sourceCoefficient_pair_1_6
  · exact sourceCoefficient_pair_1_7
  · exact sourceCoefficient_pair_1_8
  · exact sourceCoefficient_pair_1_9

/-- Quadratic coefficient certificate with fixed first index 2. -/
theorem sourceCoefficient_pair_left_2 (right : Fin 10)
    (hlt : (2 : Fin 10) < right) :
    sourcePairCoefficient 2 right = quadraticGateCoefficient 2 right := by
  fin_cases right
  · change (2 : Nat) < 0 at hlt
    omega
  · change (2 : Nat) < 1 at hlt
    omega
  · change (2 : Nat) < 2 at hlt
    omega
  · exact sourceCoefficient_pair_2_3
  · exact sourceCoefficient_pair_2_4
  · exact sourceCoefficient_pair_2_5
  · exact sourceCoefficient_pair_2_6
  · exact sourceCoefficient_pair_2_7
  · exact sourceCoefficient_pair_2_8
  · exact sourceCoefficient_pair_2_9

end QEC.Coding.Why24AppendixANF
