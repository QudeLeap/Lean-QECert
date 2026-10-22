import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventUniverse

/-! # Derived polynomial cost for the actual event-universe preprocessing -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

def rawUniverseBudget (n : ℕ) : ℕ :=
  13*n^4+n^3+n^2+n+n^4*(100000*(n+1)^2+2)

theorem rawEventUniverse_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (rawEventUniverseQuery P J hr).2 ≤ rawUniverseBudget (Fintype.card (Triangle P)) := by
  have ht := fourTuplesQuery_cost_le (triangleInputList P)
  rw [triangleInputList_length] at ht
  have hf := filterMapQuery_cost_le (candidateEventQuery P J hr)
    (fourTuplesQuery (triangleInputList P)).1 (100000*(Fintype.card (Triangle P)+1)^2+1) (by
      intro L hL
      apply candidateEventQuery_cost_le P J hr L
      apply fourTuples_entry_length (triangleInputList P) L
      simpa only [fourTuplesQuery_value] using hL)
  rw [fourTuplesQuery_value,fourTuples_length,triangleInputList_length] at hf
  dsimp only [rawEventUniverseQuery,rawUniverseBudget]
  rw [fourTuplesQuery_value]
  norm_num only [Nat.add_assoc] at hf
  omega

def eventUniverseBudget (n : ℕ) : ℕ :=
  rawUniverseBudget n+(n^4+1)^2*(24*(n+1)+330)

theorem eventUniverseQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (eventUniverseQuery P J hr).2 ≤ eventUniverseBudget (Fintype.card (Triangle P)) := by
  classical
  let raw := rawEventUniverseQuery P J hr
  let unique := dedupQuery (eventEqQuery P J r) raw.1
  have hrlen : raw.1.length ≤ Fintype.card (Triangle P)^4 := rawEventUniverse_length_le P J hr
  have hulen : unique.1.length ≤ Fintype.card (Triangle P)^4 := by
    rw [dedupQuery_value _ (eventEqQuery_correct P J r)]
    exact (List.dedup_sublist raw.1).length_le.trans hrlen
  have hd := dedupQuery_cost_le (eventEqQuery P J r) (eventEqQuery_correct P J r)
    (16*(Fintype.card (Triangle P)+1)+219) (eventEqQuery_cost_le P J r) raw.1
  have hd' : unique.2 ≤ (Fintype.card (Triangle P)^4+1)^2*(16*(Fintype.card (Triangle P)+1)+220) := by
    apply hd.trans
    apply Nat.mul_le_mul_right
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hrlen 1) 2
  have hs := sortQuery_cost_le (eventCompareQuery P J r) (eventPriorityLE P J r)
    (eventCompareQuery_priority_correct P J r) (8*(Fintype.card (Triangle P)+1)+109)
    (eventCompareQuery_cost_le P J r) unique.1
  have hs' : (sortQuery (eventCompareQuery P J r) unique.1).2 ≤
      (Fintype.card (Triangle P)^4+1)^2*(8*(Fintype.card (Triangle P)+1)+110) := by
    apply hs.trans
    apply Nat.mul_le_mul_right
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hulen 1) 2
  have hrCost := rawEventUniverse_cost_le P J hr
  dsimp only [eventUniverseQuery,eventUniverseBudget]
  dsimp only [raw,unique] at hd' hs' hrCost ⊢
  nlinarith

/-- A fixed exponent and coefficient, independent of presentation size and depth. -/
theorem eventUniverseBudget_polynomial (n : ℕ) : eventUniverseBudget n ≤ 1000000*(n+1)^10 := by
  let slack := 1000000*n^10+9999976*n^9+44999646*n^8+120000000*n^7+
    209900000*n^6+251799952*n^5+209899277*n^4+119999999*n^3+
    44999999*n^2+9999975*n+999646
  have he : eventUniverseBudget n+slack = 1000000*(n+1)^10 := by
    dsimp [eventUniverseBudget,rawUniverseBudget,slack]
    ring
  rw [← he]
  exact Nat.le_add_right _ _

end QEC.Coding.BDL26RandomPerturbation
