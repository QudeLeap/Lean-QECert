import QEC.Coding.QuditQubitConversion.AppendixANF.Quadratic.Data

/-!
# Quadratic WHY24 ANF coefficient block D

This module contains 10 independent normalized coefficient certificates.
It imports the compiled source tensor and contains no Boolean-input enumeration.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_5_6 :
    sourcePairCoefficient 5 6 = quadraticGateCoefficient 5 6 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_5_7 :
    sourcePairCoefficient 5 7 = quadraticGateCoefficient 5 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_5_8 :
    sourcePairCoefficient 5 8 = quadraticGateCoefficient 5 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_5_9 :
    sourcePairCoefficient 5 9 = quadraticGateCoefficient 5 9 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_6_7 :
    sourcePairCoefficient 6 7 = quadraticGateCoefficient 6 7 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_6_8 :
    sourcePairCoefficient 6 8 = quadraticGateCoefficient 6 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_6_9 :
    sourcePairCoefficient 6 9 = quadraticGateCoefficient 6 9 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_7_8 :
    sourcePairCoefficient 7 8 = quadraticGateCoefficient 7 8 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_7_9 :
    sourcePairCoefficient 7 9 = quadraticGateCoefficient 7 9 := by
  decide

set_option maxRecDepth 2048 in
theorem sourceCoefficient_pair_8_9 :
    sourcePairCoefficient 8 9 = quadraticGateCoefficient 8 9 := by
  decide

/-- Quadratic coefficient certificate with fixed first index 5. -/
theorem sourceCoefficient_pair_left_5 (right : Fin 10)
    (hlt : (5 : Fin 10) < right) :
    sourcePairCoefficient 5 right = quadraticGateCoefficient 5 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_5_6
  · exact sourceCoefficient_pair_5_7
  · exact sourceCoefficient_pair_5_8
  · exact sourceCoefficient_pair_5_9

/-- Quadratic coefficient certificate with fixed first index 6. -/
theorem sourceCoefficient_pair_left_6 (right : Fin 10)
    (hlt : (6 : Fin 10) < right) :
    sourcePairCoefficient 6 right = quadraticGateCoefficient 6 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_6_7
  · exact sourceCoefficient_pair_6_8
  · exact sourceCoefficient_pair_6_9

/-- Quadratic coefficient certificate with fixed first index 7. -/
theorem sourceCoefficient_pair_left_7 (right : Fin 10)
    (hlt : (7 : Fin 10) < right) :
    sourcePairCoefficient 7 right = quadraticGateCoefficient 7 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_7_8
  · exact sourceCoefficient_pair_7_9

/-- Quadratic coefficient certificate with fixed first index 8. -/
theorem sourceCoefficient_pair_left_8 (right : Fin 10)
    (hlt : (8 : Fin 10) < right) :
    sourcePairCoefficient 8 right = quadraticGateCoefficient 8 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_8_9

end QEC.Coding.Why24AppendixANF
