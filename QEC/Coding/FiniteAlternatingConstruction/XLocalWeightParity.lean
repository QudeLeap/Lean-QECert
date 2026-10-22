import QEC.Coding.FiniteAlternatingConstruction.Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite parity counting for RX local cleaning

This module proves the arithmetic step in the proof of the source lemma
`cleaning-syndrome-Yx`. It does not construct local corrections or assume a
boundary-weight estimate. The geometric construction must separately identify
the four region parities and bound its crossings by `pieceCrossingCost`.
-/

namespace QEC.Coding.BDL26XLocalWeightParity

open scoped BigOperators

/-- Hamming weight of one binary coordinate. -/
def bitWeight (b : ZMod 2) : ℕ := if b = 0 then 0 else 1

/-- Crossing budget of an even-parity piece with two layers and two strips. -/
def pieceCrossingCost (a b l r : ZMod 2) : ℕ :=
  bitWeight a + bitWeight b + bitWeight l + bitWeight r - bitWeight (a + b)

theorem bitWeight_le_add (a b : ZMod 2) :
    bitWeight a ≤ bitWeight (a + b) + bitWeight b := by
  fin_cases a <;> fin_cases b <;> decide

theorem pieceCrossingCost_le_twice_second (a b l r : ZMod 2) :
    pieceCrossingCost a b l r ≤
      bitWeight b + bitWeight b + bitWeight l + bitWeight r := by
  have h := bitWeight_le_add a b
  unfold pieceCrossingCost
  omega

theorem pieceCrossingCost_swap (a b l r : ZMod 2) :
    pieceCrossingCost a b l r = pieceCrossingCost b a l r := by
  simp only [pieceCrossingCost, add_comm a b, Nat.add_comm (bitWeight a) (bitWeight b)]

/-- The correction may change the first layer arbitrarily. If the untouched
second layer has smaller total parity weight, the total crossing budget is
bounded by the original four-region parity weight. -/
theorem sum_pieceCrossingCost_le_of_second_layer
    {J : Type*} [Fintype J]
    (originalFirst originalSecond changedFirst left right : J → ZMod 2)
    (hLayer : (∑ j, bitWeight (originalSecond j)) ≤
      ∑ j, bitWeight (originalFirst j)) :
    (∑ j, pieceCrossingCost (changedFirst j) (originalSecond j) (left j) (right j)) ≤
      ∑ j, (bitWeight (originalFirst j) + bitWeight (originalSecond j) +
        bitWeight (left j) + bitWeight (right j)) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => pieceCrossingCost_le_twice_second
      (changedFirst j) (originalSecond j) (left j) (right j))
  simp only [Finset.sum_add_distrib] at h ⊢
  omega

/-- Swapping the two layers gives the other branch of the source choice. -/
theorem sum_pieceCrossingCost_le_of_first_layer
    {J : Type*} [Fintype J]
    (originalFirst originalSecond changedSecond left right : J → ZMod 2)
    (hLayer : (∑ j, bitWeight (originalFirst j)) ≤
      ∑ j, bitWeight (originalSecond j)) :
    (∑ j, pieceCrossingCost (originalFirst j) (changedSecond j) (left j) (right j)) ≤
      ∑ j, (bitWeight (originalFirst j) + bitWeight (originalSecond j) +
        bitWeight (left j) + bitWeight (right j)) := by
  have h := sum_pieceCrossingCost_le_of_second_layer
    originalSecond originalFirst changedSecond left right hLayer
  have hCost :
      (∑ j, pieceCrossingCost (originalFirst j) (changedSecond j) (left j) (right j)) =
      ∑ j, pieceCrossingCost (changedSecond j) (originalFirst j) (left j) (right j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact pieceCrossingCost_swap _ _ _ _
  rw [hCost]
  simp only [Finset.sum_add_distrib] at h ⊢
  omega

/-- Coefficients of the four layer-to-strip crossings followed by the
strip-to-strip crossing. No witness or preimage is selected by choice. -/
def pieceCrossingCoefficients (a b l r : ZMod 2) (i : Fin 5) : ZMod 2 :=
  if a + b = 0 then
    if i = 0 then a else if i = 2 then b else if i = 4 then r else 0
  else
    if i = 0 then a * l else if i = 1 then a * r else
      if i = 2 then b * l else if i = 3 then b * r else 0

/-- Every even four-region word has the displayed explicit crossing chain,
with the exact source cost bound (the final edge has weight two). -/
theorem pieceCrossingCoefficients_spec (a b l r : ZMod 2)
    (hEven : a + b + l + r = 0) :
    let c := pieceCrossingCoefficients a b l r
    c 0 + c 1 = a ∧ c 2 + c 3 = b ∧
      c 0 + c 2 + c 4 = l ∧ c 1 + c 3 + c 4 = r ∧
      bitWeight (c 0) + bitWeight (c 1) + bitWeight (c 2) +
        bitWeight (c 3) + 2 * bitWeight (c 4) ≤ pieceCrossingCost a b l r := by
  dsimp only
  fin_cases a <;> fin_cases b <;> fin_cases l <;> fin_cases r
  all_goals
    first
    | exact False.elim ((of_decide_eq_false rfl) hEven)
    | (repeat' apply And.intro) <;> (first | rfl | decide)

end QEC.Coding.BDL26XLocalWeightParity
