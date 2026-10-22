import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.Data

/-!
# Quadratic WHY24 ANF coefficient block C

This module contains 11 independent normalized coefficient certificates.
It imports the compiled source tensor and contains no Boolean-input enumeration.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_4 :
    sourcePairCoefficient 3 4 = quadraticGateCoefficient 3 4 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_5 :
    sourcePairCoefficient 3 5 = quadraticGateCoefficient 3 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_6 :
    sourcePairCoefficient 3 6 = quadraticGateCoefficient 3 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_7 :
    sourcePairCoefficient 3 7 = quadraticGateCoefficient 3 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_8 :
    sourcePairCoefficient 3 8 = quadraticGateCoefficient 3 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_3_9 :
    sourcePairCoefficient 3 9 = quadraticGateCoefficient 3 9 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_4_5 :
    sourcePairCoefficient 4 5 = quadraticGateCoefficient 4 5 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_4_6 :
    sourcePairCoefficient 4 6 = quadraticGateCoefficient 4 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_4_7 :
    sourcePairCoefficient 4 7 = quadraticGateCoefficient 4 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_4_8 :
    sourcePairCoefficient 4 8 = quadraticGateCoefficient 4 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_4_9 :
    sourcePairCoefficient 4 9 = quadraticGateCoefficient 4 9 := by
  decide

/-- Quadratic coefficient certificate with fixed first index 3. -/
theorem sourceCoefficient_pair_left_3 (right : Fin 10)
    (hlt : (3 : Fin 10) < right) :
    sourcePairCoefficient 3 right = quadraticGateCoefficient 3 right := by
  fin_cases right
  · change (3 : Nat) < 0 at hlt
    omega
  · change (3 : Nat) < 1 at hlt
    omega
  · change (3 : Nat) < 2 at hlt
    omega
  · change (3 : Nat) < 3 at hlt
    omega
  · exact sourceCoefficient_pair_3_4
  · exact sourceCoefficient_pair_3_5
  · exact sourceCoefficient_pair_3_6
  · exact sourceCoefficient_pair_3_7
  · exact sourceCoefficient_pair_3_8
  · exact sourceCoefficient_pair_3_9

/-- Quadratic coefficient certificate with fixed first index 4. -/
theorem sourceCoefficient_pair_left_4 (right : Fin 10)
    (hlt : (4 : Fin 10) < right) :
    sourcePairCoefficient 4 right = quadraticGateCoefficient 4 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_4_5
  · exact sourceCoefficient_pair_4_6
  · exact sourceCoefficient_pair_4_7
  · exact sourceCoefficient_pair_4_8
  · exact sourceCoefficient_pair_4_9

end QEC.Coding.Why24AppendixANF
